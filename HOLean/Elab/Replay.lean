/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Elab.Term
import HOLean.Derived
import HOLean.Elab.Cert
import HOLean.Elab.ProvTrace

/-!
# Replay HOL traces into Lean `Provable` proofs

`buildProvable` walks a `ProvTrace` and assembles a kernel `Provable` term
with `mkApp*` of LCF constructors / derived rules.  Side conditions use
connective `HasType` lemmas (`HasType.tru`, `HasType.mkEq`, …), not
`infer = some` reduction, `sorry`, extra axioms, or `native_decide`.
-/

open Lean Meta Elab Term

namespace HOLean.Elab

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

/-- Lean name of a previously emitted `{leanN}_hol_prov` theorem. -/
def resolveNamedProv (leanN : Lean.Name) : MetaM Lean.Name := do
  let n := holProvName leanN
  unless (← getEnv).find? n |>.isSome do
    throwError "HOLean: no `_hol_prov` certificate for `{leanN}`"
  return n

/-- Assemble a `Provable` term from an LCF derivation trace. -/
partial def buildProvable (decls : Array HolDecl) (envE connE : Expr) :
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
    let thmN ← liftMetaM do resolveNamedProv n
    weakenTraceProof decls (mkConst thmN)
  | .eqMp hEq hP => do
    let pEq ← buildProvable decls envE connE hEq
    let pP ← buildProvable decls envE connE hP
    liftMetaM do mkAppM ``Provable.eqMp #[pEq, pP]
  | .eqSym h => do
    let p ← buildProvable decls envE connE h
    liftMetaM do
      mkAppOptM ``Provable.eq_sym
        #[some envE, some connE, none, none, none, none, some p]
  | .instType θ h => do
    let p ← buildProvable decls envE connE h
    liftMetaM do mkAppM ``Provable.instType #[toExpr θ, p]
  | .assume p =>
    throwError "HOLean: ASSUME is not certified for closed theorems ({repr p})"
  | .hole =>
    throwError "HOLean: incomplete proof (unsolved HOL goal)"

/-- Type-check a reconstructed `Provable` proof of `⊢ stmt` in `envE`. -/
def elabProvable (decls : Array HolDecl) (envE connE : Expr) (stmt : Tm)
    (tr : ProvTrace) : TermElabM Expr := do
  if tr.usesAssume then
    throwError "HOLean: tactic script uses `hassumption`; closed theorems cannot \
      emit a `Provable` certificate for ASSUME"
  if tr.hasHole then
    throwError "HOLean: incomplete proof (unsolved HOL goal)"
  let goalType := mkApp3 (mkConst ``Provable) envE mkNilTmList (toExpr stmt)
  let proof ← buildProvable decls envE connE tr
  liftMetaM do assertKernelProof proof
  unless ← isDefEq (← inferType proof) goalType do
    throwError "HOLean: reconstructed proof has the wrong type\
      {indentExpr (← inferType proof)}\nexpected{indentExpr goalType}"
  return proof

end HOLean.Elab
