/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Elab.Tactic
import HOLean.Derived
import HOLean.Elab.Cert
import HOLean.Elab.ProvTrace

/-!
# Replay HOL traces into Lean `Provable` proofs

Two backends, neither of which uses `sorry`, axioms, or `native_decide`:

* **B** (`buildProvB`): assemble a `Provable` term with `mkApp*`
* **C** (`buildProvC`): start from a metavariable and run Lean `MVarId.apply`
  / `assignIfDefEq`, mirroring the HOL steps

`HasType` side conditions are built from connective lemmas (`HasType.tru`,
`HasType.mkEq`, …), not from `infer = some` reduction.
-/

open Lean Meta Elab Term

namespace HOLean.Elab

/-- Count nodes in a proof term (olean-size proxy). -/
partial def exprSize : Expr → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ d b _ => 1 + exprSize d + exprSize b
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e => exprSize e
  | .proj _ _ e => 1 + exprSize e
  | _ => 1

/-- Reject `sorry` and `native_decide` (`ofReduceBool` / `ofReduceNat`). -/
def assertKernelProof (e : Expr) : MetaM Unit := do
  if e.hasSorry then
    throwError "HOLean: reconstructed proof contains sorry"
  if let some bad := e.find? fun
      | .const n _ =>
        n == ``Lean.ofReduceBool || n == ``Lean.ofReduceNat || n == ``Lean.trustCompiler
      | _ => false
    then
      throwError "HOLean: reconstructed proof uses `{bad.getAppFn}` (native reduction)"

/-- `HasType env Γ t ?α`, returning the synthesized type. -/
partial def elabHasType (envE connE : Expr) (t : Tm) (Γ : List Ty) :
    MetaM (Expr × Ty) := do
  let ΓE := toExpr Γ
  let tryConn (n : Lean.Name) (extra : Array (Option Expr)) : MetaM Expr :=
    mkAppOptM n (#[some envE, some connE, some ΓE] ++ extra)
  match t with
  | .const n τ =>
    if n == truName && τ == .bool then
      let pf ← tryConn ``HasType.tru #[]
      return (pf, .bool)
    else if n == falsumName && τ == .bool then
      let pf ← tryConn ``HasType.falsum #[]
      return (pf, .bool)
    else if n == andName && τ == andTy then
      let pf ← tryConn ``HasType.andConst #[]
      return (pf, andTy)
    else if n == impName && τ == impTy then
      let pf ← tryConn ``HasType.impConst #[]
      return (pf, impTy)
    else if n == notName && τ == notTy then
      let pf ← tryConn ``HasType.notConst #[]
      return (pf, notTy)
    else if n == orName && τ == orTy then
      let pf ← tryConn ``HasType.orConst #[]
      return (pf, orTy)
    else if n == eqName then
      match τ with
      | α ↝ β ↝ .bool =>
        unless α == β do
          throwError "HOLean: equality constant domain mismatch"
        let hasEq ← mkAppM ``HOLean.Elab.hasEq_of_conn #[connE]
        let pf ← mkAppOptM ``HasType.eqConst
          #[some envE, some hasEq, some ΓE, some (toExpr α)]
        return (pf, α ↝ α ↝ .bool)
      | _ => throwError "HOLean: cannot type `{n}` at {repr τ}"
    else
      throwError "HOLean: no HasType lemma for constant `{n}`"
  | .app (.app (.const n τ) p) q =>
    if n == andName then
      let (hp, _) ← elabHasType envE connE p Γ
      let (hq, _) ← elabHasType envE connE q Γ
      let pf ← tryConn ``HasType.and #[some (toExpr p), some (toExpr q), some hp, some hq]
      return (pf, .bool)
    else if n == impName then
      let (hp, _) ← elabHasType envE connE p Γ
      let (hq, _) ← elabHasType envE connE q Γ
      let pf ← tryConn ``HasType.imp #[some (toExpr p), some (toExpr q), some hp, some hq]
      return (pf, .bool)
    else if n == orName then
      let (hp, _) ← elabHasType envE connE p Γ
      let (hq, _) ← elabHasType envE connE q Γ
      let pf ← tryConn ``HasType.or #[some (toExpr p), some (toExpr q), some hp, some hq]
      return (pf, .bool)
    else if n == eqName then
      match τ with
      | α ↝ _ ↝ .bool =>
        let (hs, αs) ← elabHasType envE connE p Γ
        let (ht, _) ← elabHasType envE connE q Γ
        unless αs == α do
          throwError "HOLean: equality type mismatch"
        let hasEq ← mkAppM ``HOLean.Elab.hasEq_of_conn #[connE]
        let pf ← mkAppOptM ``HasType.mkEq
          #[some envE, some hasEq, some ΓE, some (toExpr p), some (toExpr q),
            some (toExpr αs), some hs, some ht]
        return (pf, .bool)
      | _ =>
        let (hf, tf) ← elabHasType envE connE (.app (.const n τ) p) Γ
        let (ha, _) ← elabHasType envE connE q Γ
        match tf with
        | .arrow _ β =>
          let pf ← mkAppM ``HasType.app #[hf, ha]
          return (pf, β)
        | _ => throwError "HOLean: expected a function type"
    else
      let (hf, tf) ← elabHasType envE connE (.app (.const n τ) p) Γ
      let (ha, _) ← elabHasType envE connE q Γ
      match tf with
      | .arrow _ β =>
        let pf ← mkAppM ``HasType.app #[hf, ha]
        return (pf, β)
      | _ => throwError "HOLean: expected a function type"
  | .app f a =>
    let (hf, tf) ← elabHasType envE connE f Γ
    let (ha, _) ← elabHasType envE connE a Γ
    match tf with
    | .arrow _ β =>
      let pf ← mkAppM ``HasType.app #[hf, ha]
      return (pf, β)
    | _ => throwError "HOLean: expected a function type"
  | .lam α b =>
    let (ht, β) ← elabHasType envE connE b (α :: Γ)
    let pf ← mkAppM ``HasType.lam #[ht]
    return (pf, α ↝ β)
  | .fvar x α =>
    let pf ← mkAppOptM ``HasType.fvar
      #[some envE, some ΓE, some (toExpr x), some (toExpr α)]
    return (pf, α)
  | .bvar _ =>
    throwError "HOLean: HasType for bvar is not replayed (open term)"

/-- `t.infer env [] = some .bool` from a connective `HasType` derivation. -/
def mkInferBoolProof (envE connE : Expr) (stmt : Tm) : TermElabM Expr := do
  let (ht, α) ← liftMetaM do elabHasType envE connE stmt []
  unless α == .bool do
    throwError "HOLean: statement is not a boolean"
  liftMetaM do mkAppM ``HasType.infer_of #[ht]

/-- `Env.LE` from `envExprFromDecls fromD` to `envExprFromDecls toD`. -/
def mkEnvLe (fromD toD : Array HolDecl) : TermElabM Expr := do
  unless fromD.size ≤ toD.size do
    throwError "HOLean: environment is not an extension"
  let mut envE := envExprFromDecls fromD
  let mut le ← liftMetaM do mkAppM ``Env.LE.refl #[envE]
  for d in toD[fromD.size:] do
    match d with
    | .defn _ n ty rhs =>
      let holNExpr := toExpr n
      let tyExpr := toExpr ty
      let rhsExpr := toExpr rhs
      let freshTy ← liftMetaM do
        mkEqApp
          (mkApp2 (mkConst ``Env.constants) envE holNExpr)
          (mkOptionNone (mkConst ``Ty))
      let fresh ← proveByRfl freshTy
      let step ← liftMetaM do
        mkAppOptM ``Env.LE.addDef_of_fresh
          #[some envE, some holNExpr, some tyExpr, some rhsExpr, some fresh]
      le ← liftMetaM do mkAppM ``Env.LE.trans #[le, step]
      envE := mkApp4 (mkConst ``Env.addDef) envE holNExpr tyExpr rhsExpr
    | .thm _ _ stmt =>
      let step ← liftMetaM do mkAppM ``Env.LE.addAxiom #[envE, toExpr stmt]
      le ← liftMetaM do mkAppM ``Env.LE.trans #[le, step]
      envE := mkApp2 (mkConst ``Env.addAxiom) envE (toExpr stmt)
  return le

def extractProvEnv? (proofTy : Expr) : Option Expr :=
  match proofTy with
  | .app (.app (.app (.const ``Provable _) e) _) _ => some e
  | _ => none

/-- Weaken a `Provable` proof into `envExprFromDecls decls`. -/
def weakenTraceProof (decls : Array HolDecl) (proof : Expr) : TermElabM Expr := do
  let target := envExprFromDecls decls
  let proofTy ← liftMetaM do whnf (← inferType proof)
  let some proofEnv := extractProvEnv? proofTy
    | throwError "HOLean: expected a `Provable` proof{indentExpr proofTy}"
  if ← liftMetaM do isDefEq proofEnv target then
    return proof
  let mut acc : Array HolDecl := #[]
  for d in decls do
    if ← liftMetaM do isDefEq (envExprFromDecls acc) proofEnv then
      let hle ← mkEnvLe acc decls
      return ← liftMetaM do mkAppM ``HOLean.Elab.cert_prov_weaken #[hle, proof]
    acc := acc.push d
  if ← liftMetaM do isDefEq (envExprFromDecls acc) proofEnv then
    return proof
  throwError "HOLean: cannot weaken kernel proof into the current environment"

def holProvName (leanN : Lean.Name) : Lean.Name :=
  leanN.appendAfter "_hol_prov"

def holProvCName (leanN : Lean.Name) : Lean.Name :=
  leanN.appendAfter "_hol_prov_C"

/-- Resolve a previously emitted `_hol_prov` / `_hol_prov_C` constant. -/
def resolveNamedProv (leanN : Lean.Name) (preferC : Bool) : MetaM Lean.Name := do
  let env ← getEnv
  if preferC then
    let cN := holProvCName leanN
    if env.find? cN |>.isSome then
      return cN
  let bN := holProvName leanN
  if env.find? bN |>.isSome then
    return bN
  throwError "HOLean: no `_hol_prov` certificate for `{leanN}`"

/-- Proof-producing backend: `mkApp*` of `Provable` constructors / derived rules. -/
partial def buildProvB (decls : Array HolDecl) (envE connE : Expr) :
    ProvTrace → TermElabM Expr
  | .refl t α => do
    let (ht, α') ← liftMetaM do elabHasType envE connE t []
    unless α' == α do
      throwError "HOLean: REFL type mismatch: inferred {repr α'}, expected {repr α}"
    liftMetaM do
      mkAppOptM ``Provable.refl
        #[some envE, some (toExpr t), some (toExpr α), some ht]
  | .truth => do
    liftMetaM do mkAppOptM ``Provable.tru_intro #[some envE, some connE]
  | .named n => do
    let thmN ← liftMetaM do resolveNamedProv n false
    weakenTraceProof decls (mkConst thmN)
  | .eqMp hEq hP => do
    let pEq ← buildProvB decls envE connE hEq
    let pP ← buildProvB decls envE connE hP
    liftMetaM do mkAppM ``Provable.eqMp #[pEq, pP]
  | .eqSym h => do
    let p ← buildProvB decls envE connE h
    liftMetaM do
      mkAppOptM ``Provable.eq_sym
        #[some envE, some connE, none, none, none, none, some p]
  | .instType θ h => do
    let p ← buildProvB decls envE connE h
    liftMetaM do mkAppM ``Provable.instType #[toExpr θ, p]
  | .assume p =>
    throwError "HOLean: ASSUME is not certified for closed theorems ({repr p})"

/-- `apply e` expecting `expected` subgoals; reverts the metavariable context on failure. -/
def tryApplyN (g : MVarId) (e : Expr) (expected : Nat) : MetaM (Option (List MVarId)) :=
  observing? do
    let gs ← g.apply e
    unless gs.length == expected do
      throwError "HOLean: apply produced {gs.length} goals, expected {expected}"
    pure gs

/-- Lean tactic-replay backend: `MVarId.apply` / `assignIfDefEq`.

Returns whether any step fell back to the B constructor (`mkApp*`). -/
partial def replayApply (envE connE : Expr) (decls : Array HolDecl) (g : MVarId) :
    ProvTrace → TermElabM Bool
  | .truth => do
    let e ← liftMetaM do mkAppOptM ``Provable.tru_intro #[some envE, some connE]
    liftMetaM do g.assignIfDefEq e
    return false
  | .named n => do
    let thmN ← liftMetaM do resolveNamedProv n true
    let proof ← weakenTraceProof decls (mkConst thmN)
    liftMetaM do g.assignIfDefEq proof
    return false
  | .refl t α => do
    let (ht, _) ← liftMetaM do elabHasType envE connE t []
    let e ← liftMetaM do
      mkAppOptM ``Provable.refl
        #[some envE, some (toExpr t), some (toExpr α), some ht]
    liftMetaM do g.assignIfDefEq e
    return false
  | .eqMp hEq hP => do
    let hinted ← liftMetaM do
      mkAppOptM ``Provable.eqMp #[some envE, some mkNilTmList, some mkNilTmList]
    let gs? ← liftMetaM do
      match ← tryApplyN g hinted 2 with
      | some gs => pure (some gs)
      | none => tryApplyN g (mkConst ``Provable.eqMp) 2
    match gs? with
    | some [gEq, gP] =>
      let fb1 ← replayApply envE connE decls gEq hEq
      let fb2 ← replayApply envE connE decls gP hP
      return fb1 || fb2
    | _ =>
      -- `apply Provable.eqMp` does not unify `Γ ++ Δ` with `[]`.
      let pEq ← buildProvB decls envE connE hEq
      let pP ← buildProvB decls envE connE hP
      let e ← liftMetaM do mkAppM ``Provable.eqMp #[pEq, pP]
      liftMetaM do g.assignIfDefEq e
      return true
  | .eqSym h => do
    let hinted ← liftMetaM do
      mkAppOptM ``Provable.eq_sym #[some envE, some connE, some mkNilTmList]
    let gs? ← liftMetaM do
      match ← tryApplyN g hinted 1 with
      | some gs => pure (some gs)
      | none => tryApplyN g (mkConst ``Provable.eq_sym) 1
    match gs? with
    | some [g'] => replayApply envE connE decls g' h
    | _ =>
      let p ← buildProvB decls envE connE h
      let e ← liftMetaM do
        mkAppOptM ``Provable.eq_sym
          #[some envE, some connE, none, none, none, none, some p]
      liftMetaM do g.assignIfDefEq e
      return true
  | .instType θ h => do
    let eθ := toExpr θ
    let hinted ← liftMetaM do
      mkAppOptM ``Provable.instType
        #[some envE, some mkNilTmList, none, some eθ]
    let gs? ← liftMetaM do
      match ← tryApplyN g hinted 1 with
      | some gs => pure (some gs)
      | none =>
        try
          let e ← mkAppM ``Provable.instType #[eθ]
          tryApplyN g e 1
        catch _ =>
          tryApplyN g (mkConst ``Provable.instType) 1
    match gs? with
    | some [g'] => replayApply envE connE decls g' h
    | _ =>
      let p ← buildProvB decls envE connE h
      let e ← liftMetaM do mkAppM ``Provable.instType #[eθ, p]
      liftMetaM do g.assignIfDefEq e
      return true
  | .assume p =>
    throwError "HOLean: ASSUME is not certified for closed theorems ({repr p})"

def buildProvC (decls : Array HolDecl) (envE connE : Expr) (goalType : Expr)
    (tr : ProvTrace) : TermElabM (Expr × Bool) := do
  let mvar ← mkFreshExprMVar goalType
  let fallback ← replayApply envE connE decls mvar.mvarId! tr
  let val ← instantiateMVars mvar
  if val.hasExprMVar then
    throwError "HOLean: tactic replay left metavariables"
  return (val, fallback)

/-- Result of replaying a tactic script as `Provable` proofs. -/
structure ReplayResult where
  proofB : Expr
  proofC : Expr
  sizeB : Nat
  sizeC : Nat
  fallbackToB : Bool

def replayCertified (decls : Array HolDecl) (envE connE : Expr) (stmt : Tm)
    (tr : ProvTrace) : TermElabM ReplayResult := do
  if tr.usesAssume then
    throwError "HOLean: tactic script uses `hassumption`; closed theorems cannot \
      emit a `Provable` certificate for ASSUME"
  let goalType := mkApp3 (mkConst ``Provable) envE mkNilTmList (toExpr stmt)
  let proofB ← buildProvB decls envE connE tr
  liftMetaM do assertKernelProof proofB
  unless ← isDefEq (← inferType proofB) goalType do
    throwError "HOLean: B proof has the wrong type{indentExpr (← inferType proofB)}\n\
      expected{indentExpr goalType}"
  let (proofC, fallbackToB) ← buildProvC decls envE connE goalType tr
  liftMetaM do assertKernelProof proofC
  unless ← isDefEq (← inferType proofC) goalType do
    throwError "HOLean: C proof has the wrong type{indentExpr (← inferType proofC)}\n\
      expected{indentExpr goalType}"
  return {
    proofB
    proofC
    sizeB := exprSize (← instantiateMVars proofB)
    sizeC := exprSize (← instantiateMVars proofC)
    fallbackToB
  }

end HOLean.Elab
