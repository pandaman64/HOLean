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

theorem listGetElem?_zero (α : Ty) (Γ : List Ty) :
    (α :: Γ)[0]? = some α :=
  rfl

theorem listGetElem?_succ (α : Ty) (Γ : List Ty) (n : Nat) (β : Ty)
    (h : Γ[n]? = some β) : (α :: Γ)[n + 1]? = some β := by
  simpa [List.getElem?_cons_succ] using h

/-- Proof of `Γ[i]? = some α` for a concrete context, used to replay `HasType.bvar`. -/
partial def mkListGetElem? (Γ : List Ty) (i : Nat) : MetaM (Expr × Ty) := do
  match Γ, i with
  | [], _ =>
    throwError "HOLean: unbound bvar {i}"
  | α :: rest, 0 =>
    let pf ← mkAppOptM ``listGetElem?_zero
      #[some (toExpr α), some (toExpr rest)]
    return (pf, α)
  | α :: rest, n + 1 =>
    let (ih, β) ← mkListGetElem? rest n
    let pf ← mkAppOptM ``listGetElem?_succ
      #[some (toExpr α), some (toExpr rest), some (toExpr n), some (toExpr β), some ih]
    return (pf, β)

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
    else if n == selectName then
      match τ with
      | (α ↝ .bool) ↝ α' =>
        unless α == α' do
          throwError "HOLean: select constant domain mismatch"
        let hasSel ← mkAppM ``HOLean.Elab.hasSelect_of_conn #[connE]
        let pf ← mkAppOptM ``HasType.selectConst
          #[some envE, some hasSel, some ΓE, some (toExpr α)]
        return (pf, (α ↝ .bool) ↝ α)
      | _ => throwError "HOLean: cannot type `select` at {repr τ}"
    else if n == allName then
      match τ with
      | (α ↝ .bool) ↝ .bool =>
        let pf ← tryConn ``HasType.allConst #[some (toExpr α)]
        return (pf, (α ↝ .bool) ↝ .bool)
      | _ => throwError "HOLean: cannot type `all` at {repr τ}"
    else if n == exName then
      match τ with
      | (α ↝ .bool) ↝ .bool =>
        let pf ← tryConn ``HasType.exConst #[some (toExpr α)]
        return (pf, (α ↝ .bool) ↝ .bool)
      | _ => throwError "HOLean: cannot type `ex` at {repr τ}"
    else
      -- User / other constants: require `env.constants n = some τ` (exact).
      let lhs := mkApp2 (mkConst ``Env.constants) envE (toExpr n)
      let rhs :=
        mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Ty) (toExpr τ)
      unless ← isDefEq lhs rhs do
        throwError "HOLean: no HasType lemma for constant `{n}` at {repr τ}"
      let eqTy ← mkEq lhs rhs
      let hconst ← mkExpectedTypeHint (← mkEqRefl lhs) eqTy
      let hinst ← mkAppM ``Ty.isInstanceOf_self #[toExpr τ]
      let pf ← mkAppOptM ``HasType.const
        #[some envE, some ΓE, some (toExpr n), some (toExpr τ), some (toExpr τ),
          some hconst, some hinst]
      return (pf, τ)
  | .app (.const n τ) P =>
    if n == allName then
      match τ with
      | (α ↝ .bool) ↝ .bool =>
        let (hP, tP) ← elabHasType envE connE P Γ
        unless tP == α ↝ .bool do
          throwError "HOLean: ∀-predicate type mismatch"
        let pf ← tryConn ``HasType.all #[some (toExpr α), some (toExpr P), some hP]
        return (pf, .bool)
      | _ => throwError "HOLean: malformed `all` constant type {repr τ}"
    else if n == exName then
      match τ with
      | (α ↝ .bool) ↝ .bool =>
        let (hP, tP) ← elabHasType envE connE P Γ
        unless tP == α ↝ .bool do
          throwError "HOLean: ∃-predicate type mismatch"
        let pf ← tryConn ``HasType.ex #[some (toExpr α), some (toExpr P), some hP]
        return (pf, .bool)
      | _ => throwError "HOLean: malformed `ex` constant type {repr τ}"
    else
      let (hf, tf) ← elabHasType envE connE (.const n τ) Γ
      let (ha, _) ← elabHasType envE connE P Γ
      match tf with
      | .arrow _ β =>
        let pf ← mkAppM ``HasType.app #[hf, ha]
        return (pf, β)
      | _ => throwError "HOLean: expected a function type"
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
  | .bvar i =>
    let (hEq, α) ← mkListGetElem? Γ i
    let pf ← mkAppOptM ``HasType.bvar
      #[some envE, some ΓE, some (toExpr α), some (toExpr i), some hEq]
    return (pf, α)

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

theorem abs_fresh_nil (x : HOLean.Name) (α : Ty) :
    ∀ p ∈ ([] : List Tm), p.freeIn x α = false := by
  intro p hp; cases hp

/-- `[(x,α,u)].Ok env` from `HasType env [] u α`. -/
theorem substOk_singleton {env : Env} {x : HOLean.Name} {α : Ty} {u : Tm}
    (hu : HasType env [] u α) : Tm.Subst.Ok env [(x, α, u)] := by
  intro y γ v hv
  simp [Tm.Subst.lookup] at hv
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hv
  exact hu

theorem substOk_nil {env : Env} : Tm.Subst.Ok env ([] : Tm.Subst) := by
  intro y γ v hv
  simp [Tm.Subst.lookup] at hv

theorem holEnv_axioms_infinity : holEnv.axioms infinityAxiom :=
  Or.inr HOLAxiom.infinity

/-- Reconstruct the sequent of a closed (or open) trace for side conditions. -/
partial def ProvTrace.evalSequent (decls : Array HolDecl) :
    ProvTrace → Option (List Tm × Tm)
  | .refl t α => some ([], Tm.mkEq α t t)
  | .trans h1 h2 => do
    let (Γ, e1) ← h1.evalSequent decls
    let (Δ, e2) ← h2.evalSequent decls
    let some (α, s, t) := Tm.destEq e1 | none
    let some (β, t', u) := Tm.destEq e2 | none
    if α == β && t == t' then
      some (Γ ++ Δ, Tm.mkEq α s u)
    else none
  | .mkComb h1 h2 => do
    let (Γ, e1) ← h1.evalSequent decls
    let (Δ, e2) ← h2.evalSequent decls
    let some (.arrow α β, f, g) := Tm.destEq e1 | none
    let some (α', x, y) := Tm.destEq e2 | none
    if α == α' then
      some (Γ ++ Δ, Tm.mkEq β (.app f x) (.app g y))
    else none
  | .abs x α h => do
    let (Γ, e) ← h.evalSequent decls
    let some (β, s, t) := Tm.destEq e | none
    some (Γ, Tm.mkEq (α ↝ β) (s.abstract x α) (t.abstract x α))
  | .beta .. => none
  | .assume p => some ([p], p)
  | .eqMp hEq hP => do
    let (Γ, e) ← hEq.evalSequent decls
    let (Δ, p) ← hP.evalSequent decls
    let some (.bool, p', q) := Tm.destEq e | none
    if p' == p then some (Γ ++ Δ, q) else none
  | .deductAntisym h1 h2 => do
    let (Γ, p) ← h1.evalSequent decls
    let (Δ, q) ← h2.evalSequent decls
    some (hypsErase q Γ ++ hypsErase p Δ, Tm.mkEq .bool p q)
  | .instType θ h => do
    let (Γ, p) ← h.evalSequent decls
    some (Γ.map (·.instTy θ), p.instTy θ)
  | .inst σ h => do
    let (Γ, p) ← h.evalSequent decls
    some (Γ.map (·.applySubst σ), p.applySubst σ)
  | .ax p => some ([], p)
  | .truth => some ([], Tm.tru)
  | .named leanN =>
    decls.findSome? fun
      | .thm ln _ stmt => if ln == leanN then some ([], stmt) else none
      | .defn .. => none
  | .eqSym h => do
    let (Γ, e) ← h.evalSequent decls
    let some (α, s, t) := Tm.destEq e | none
    some (Γ, Tm.mkEq α t s)
  | .gen x α h => do
    let (Γ, t) ← h.evalSequent decls
    some (Γ, Tm.all α (t.abstract x α))
  | .disch p h => do
    let (Γ, q) ← h.evalSequent decls
    some (Γ.filter (· != p), Tm.imp p q)
  | .hole => none

/-- `∀ p ∈ Γ, p.freeIn x α = false` by `rfl` on each concrete hypothesis. -/
def mkAbsFreshProof (Γ : List Tm) (x : HOLean.Name) (α : Ty) : TermElabM Expr := do
  match Γ with
  | [] =>
    liftMetaM do mkAppM ``abs_fresh_nil #[toExpr x, toExpr α]
  | _ =>
    throwError "HOLean: ABS with non-empty hypotheses is not yet certified for replay"

/-- Prove `σ.Ok env` for a concrete substitution (empty or singleton). -/
def mkSubstOk (envE connE : Expr) (σ : Tm.Subst) : TermElabM Expr := do
  match σ with
  | [] =>
    liftMetaM do mkAppOptM ``substOk_nil #[some envE]
  | [(x, α, u)] => do
    let (hu, α') ← liftMetaM do elabHasType envE connE u []
    unless α' == α do
      throwError "HOLean: INST replacement type mismatch"
    liftMetaM do
      mkAppOptM ``substOk_singleton
        #[some envE, some (toExpr x), some (toExpr α), some (toExpr u), some hu]
  | _ =>
    throwError "HOLean: INST with multiple substitutions is not yet replayed"

/-- Weaken an `env.axioms p` proof along subsequent `HolDecl`s. -/
def weakenAxiomsProof (fromDecls toDecls : Array HolDecl) (p : Tm) (pf : Expr) :
    TermElabM Expr := do
  unless fromDecls.size ≤ toDecls.size do
    throwError "HOLean: cannot weaken axioms proof"
  let mut envE := envExprFromDecls fromDecls
  let mut pf := pf
  for d in toDecls[fromDecls.size:] do
    match d with
    | .defn _ n ty rhs =>
      pf :=
        mkAppN (mkConst ``Env.addDef_axioms_of)
          #[envE, toExpr n, toExpr ty, toExpr rhs, toExpr p, pf]
      envE := mkApp4 (mkConst ``Env.addDef) envE (toExpr n) (toExpr ty) (toExpr rhs)
    | .thm _ _ stmt =>
      pf :=
        mkAppN (mkConst ``Env.addAxiom_axioms_of)
          #[envE, toExpr stmt, toExpr p, pf]
      envE := mkApp2 (mkConst ``Env.addAxiom) envE (toExpr stmt)
  return pf

/-- Prove `env.axioms p` for a definitional equation or HOL schema axiom. -/
def mkAxiomsProof (decls : Array HolDecl) (envE connE : Expr) (p : Tm) :
    TermElabM Expr := do
  let tryConnAx (axName : Lean.Name) (expected : Tm) : TermElabM (Option Expr) := do
    if p == expected then
      some <$> liftMetaM do mkAppOptM axName #[some envE, some connE]
    else
      pure none
  if let some pf ← tryConnAx ``Env.HasConnectives.tru_ax
      (Tm.mkEq truTy Tm.tru Tm.truDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.and_ax
      (Tm.mkEq andTy (.const andName andTy) Tm.andDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.imp_ax
      (Tm.mkEq impTy (.const impName impTy) Tm.impDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.all_ax
      (Tm.mkEq allTy (.const allName allTy) Tm.allDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.falsum_ax
      (Tm.mkEq falsumTy Tm.falsum Tm.falsumDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.not_ax
      (Tm.mkEq notTy (.const notName notTy) Tm.notDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.or_ax
      (Tm.mkEq orTy (.const orName orTy) Tm.orDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.ex_ax
      (Tm.mkEq exTy (.const exName exTy) Tm.exDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.oneOne_ax
      (Tm.mkEq oneOneTy (.const oneOneName oneOneTy) Tm.oneOneDef) then return pf
  if let some pf ← tryConnAx ``Env.HasConnectives.onto_ax
      (Tm.mkEq ontoTy (.const ontoName ontoTy) Tm.ontoDef) then return pf
  -- User `hdef` defining equation.
  match Tm.destEq p with
  | some (ty, .const n τ, rhs) =>
    if ty == τ then
      let mut prefixDecls : Array HolDecl := #[]
      for d in decls do
        match d with
        | .defn _ hn hty hrhs =>
          if hn == n && hty == ty && hrhs == rhs then
            let envBefore := envExprFromDecls prefixDecls
            let pf0 :=
              mkAppN (mkConst ``Env.addDef_axioms_self)
                #[envBefore, toExpr n, toExpr ty, toExpr rhs]
            let after := prefixDecls.push d
            return ← weakenAxiomsProof after decls p pf0
          else
            prefixDecls := prefixDecls.push d
        | .thm .. =>
          prefixDecls := prefixDecls.push d
  | _ => pure ()
  -- Infinity axiom of `holEnv`, weakened through user decls.
  if p == infinityAxiom then
    let pf0 := Lean.mkConst ``HOLean.Elab.holEnv_axioms_infinity
    return ← weakenAxiomsProof #[] decls p pf0
  throwError "HOLean: cannot prove environment axiom {repr p}"

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
  | .trans h1 h2 => do
    let p1 ← buildProvable decls envE connE h1
    let p2 ← buildProvable decls envE connE h2
    liftMetaM do mkAppM ``Provable.trans #[p1, p2]
  | .mkComb h1 h2 => do
    let p1 ← buildProvable decls envE connE h1
    let p2 ← buildProvable decls envE connE h2
    liftMetaM do mkAppM ``Provable.mkComb #[p1, p2]
  | .abs x α h => do
    let p ← buildProvable decls envE connE h
    let some (Γ, _) := h.evalSequent decls
      | throwError "HOLean: ABS: cannot reconstruct hypotheses"
    let hfresh ← mkAbsFreshProof Γ x α
    liftMetaM do
      mkAppOptM ``Provable.abs
        #[some envE, none, none, none, some (toExpr x), some (toExpr α), none,
          some p, some hfresh]
  | .beta t x α => do
    let (ht, β) ← liftMetaM do elabHasType envE connE t [α]
    liftMetaM do
      mkAppOptM ``Provable.beta
        #[some envE, some (toExpr t), some (toExpr x), some (toExpr α), some (toExpr β),
          some ht]
  | .deductAntisym h1 h2 => do
    let p1 ← buildProvable decls envE connE h1
    let p2 ← buildProvable decls envE connE h2
    liftMetaM do mkAppM ``Provable.deductAntisym #[p1, p2]
  | .inst σ h => do
    let p ← buildProvable decls envE connE h
    let hσ ← mkSubstOk envE connE σ
    liftMetaM do
      mkAppOptM ``Provable.inst
        #[some envE, none, none, some (toExpr σ), some hσ, some p]
  | .ax p => do
    let hax ← mkAxiomsProof decls envE connE p
    let (hty, α) ← liftMetaM do elabHasType envE connE p []
    unless α == .bool do
      throwError "HOLean: axiom is not a boolean"
    liftMetaM do
      mkAppOptM ``Provable.ax
        #[some envE, some (toExpr p), some hax, some hty]
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
  | .gen x α h => do
    let p ← buildProvable decls envE connE h
    liftMetaM do
      mkAppOptM ``Provable.gen_nil
        #[some envE, some connE, none, some (toExpr x), some (toExpr α), some p]
  | .disch p _ =>
    throwError "HOLean: DISCH is not certified for closed theorems ({repr p})"
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
  if tr.usesDisch then
    throwError "HOLean: tactic script uses DISCH; closed theorems cannot yet \
      emit a `Provable` certificate for discharged hypotheses"
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
