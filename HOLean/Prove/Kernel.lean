/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Prove.Typecheck
import HOLean.Syntax.Logic

/-!
# Ten HOL Light primitives as verified `ProveM` functions

Each rule returns a `CertifiedThm` whose `proof` is the corresponding
`Provable` constructor.  Failure is `ProveM.throw`.
-/

namespace HOLean
namespace Prove
namespace Hol

variable {env : Env}

/-- Wrap a sequent. -/
def mk (hyps : List Tm) (concl : Tm) (proof : Provable env hyps concl) :
    CertifiedThm env :=
  { hyps, concl, proof }

/-- `REFL t` gives `⊢ t = t`. -/
def refl (tm : Tm) : ProveM env (CertifiedThm env) := do
  let ⟨α, ht⟩ ← infer [] tm
  return mk [] (Tm.mkEq α tm tm) (Provable.refl ht.down)

/-- `TRANS`. -/
def trans (th1 th2 : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match h1 : Tm.destEq th1.concl with
  | some (α, s, t) =>
    match h2 : Tm.destEq th2.concl with
    | some (β, t', u) =>
      if hα : α = β then
        if ht : t = t' then
          return mk (th1.hyps ++ th2.hyps) (Tm.mkEq α s u) (by
            have e1 := Tm.destEq_eq h1
            have e2 := Tm.destEq_eq h2
            subst hα; subst ht
            have p1 : Provable env th1.hyps (Tm.mkEq α s t) := e1 ▸ th1.proof
            have p2 : Provable env th2.hyps (Tm.mkEq α t u) := e2 ▸ th2.proof
            exact Provable.trans p1 p2)
        else ProveM.throw "TRANS: conclusions do not join"
      else ProveM.throw "TRANS: type mismatch"
    | none => ProveM.throw "TRANS: expected equations"
  | none => ProveM.throw "TRANS: expected equations"

/-- `MK_COMB`. -/
def mkComb (th1 th2 : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match h1 : Tm.destEq th1.concl with
  | some (.arrow α β, f, g) =>
    match h2 : Tm.destEq th2.concl with
    | some (α', x, y) =>
      if hα : α = α' then
        return mk (th1.hyps ++ th2.hyps) (Tm.mkEq β (.app f x) (.app g y)) (by
          have e1 := Tm.destEq_eq h1
          have e2 := Tm.destEq_eq h2
          subst hα
          have p1 : Provable env th1.hyps (Tm.mkEq (α ↝ β) f g) := e1 ▸ th1.proof
          have p2 : Provable env th2.hyps (Tm.mkEq α x y) := e2 ▸ th2.proof
          exact Provable.mkComb p1 p2)
      else ProveM.throw "MK_COMB: domain mismatch"
    | none => ProveM.throw "MK_COMB: expected an argument equation"
  | some _ => ProveM.throw "MK_COMB: expected an equation of function type"
  | none => ProveM.throw "MK_COMB: expected an equation of function type"

/-- `ABS`: close the free variable `(x, α)` on both sides. -/
def abs (x : Name) (α : Ty) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let ⟨hfresh⟩ ← checkFreshHyps x α th.hyps
  match h1 : Tm.destEq th.concl with
  | some (β, s, t) =>
    return mk th.hyps
      (Tm.mkEq (α ↝ β) (s.abstract x α) (t.abstract x α)) (by
        have e1 := Tm.destEq_eq h1
        have p1 : Provable env th.hyps (Tm.mkEq β s t) := e1 ▸ th.proof
        exact Provable.abs p1 hfresh)
  | none => ProveM.throw "ABS: expected an equation"

/-- `BETA`: `⊢ ((λ x. t) x) = t[x]`. -/
def beta (x : Name) (α : Ty) (t : Tm) : ProveM env (CertifiedThm env) := do
  let ⟨β, ht⟩ ← infer [α] t
  return mk []
    (Tm.mkEq β (.app (.lam α t) (.fvar x α)) (t.open' (.fvar x α)))
    (Provable.beta ht.down)

/-- `ASSUME p` gives `{p} ⊢ p`. -/
def assume (p : Tm) : ProveM env (CertifiedThm env) := do
  let ⟨hp⟩ ← checkBool [] p
  return mk [p] p (Provable.assume hp)

/-- `EQ_MP`. -/
def eqMp (th1 th2 : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match h1 : Tm.destEq th1.concl with
  | some (.bool, p, q) =>
    if hp : p = th2.concl then
      return mk (th1.hyps ++ th2.hyps) q (by
        have e1 := Tm.destEq_eq h1
        subst hp
        have p1 : Provable env th1.hyps (Tm.mkEq .bool th2.concl q) := e1 ▸ th1.proof
        exact Provable.eqMp p1 th2.proof)
    else ProveM.throw "EQ_MP: left-hand side does not match the second theorem"
  | some _ => ProveM.throw "EQ_MP: expected a boolean equation"
  | none => ProveM.throw "EQ_MP: expected a boolean equation"

/-- `DEDUCT_ANTISYM_RULE`. -/
def deductAntisym (th1 th2 : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  return mk
    (hypsErase th2.concl th1.hyps ++ hypsErase th1.concl th2.hyps)
    (Tm.mkEq .bool th1.concl th2.concl)
    (Provable.deductAntisym th1.proof th2.proof)

/-- `INST_TYPE`. -/
def instType (θ : TySubst) (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  return mk
    (th.hyps.map (·.instTy θ))
    (th.concl.instTy θ)
    (Provable.instType θ th.proof)

/-- `INST` (type-preserving substitution of free variables). -/
def inst (σ : Tm.Subst) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let ⟨hσ⟩ ← checkSubst σ
  return mk
    (th.hyps.map (·.applySubst σ))
    (th.concl.applySubst σ)
    (Provable.inst hσ th.proof)

/-- A sentence already in `env.axioms`. -/
def ax (p : Tm) : ProveM env (CertifiedThm env) := do
  let ctx ← read
  let ⟨hp⟩ ← checkMemAxioms p
  return mk [] p (Provable.of_axiom ctx.wf hp)

/-- Named recall: roster lookup, then `ax`. -/
def thm (n : Name) : ProveM env (CertifiedThm env) := do
  match (← read).thms.find? (fun e => e.1 == n) with
  | none => ProveM.throw s!"no theorem `{n}`"
  | some (_, p) => ax p

/-- Defining right-hand side of a built-in `addDef` constant. -/
def builtinDef? (n : Name) : Option (Ty × Tm) :=
  if n == truName then some (truTy, Tm.truDef)
  else if n == andName then some (andTy, Tm.andDef)
  else if n == impName then some (impTy, Tm.impDef)
  else if n == allName then some (allTy, Tm.allDef)
  else if n == falsumName then some (falsumTy, Tm.falsumDef)
  else if n == notName then some (notTy, Tm.notDef)
  else if n == orName then some (orTy, Tm.orDef)
  else if n == exName then some (exTy, Tm.exDef)
  else if n == oneOneName then some (oneOneTy, Tm.oneOneDef)
  else if n == ontoName then some (ontoTy, Tm.ontoDef)
  else none

/-- Defining equation `⊢ c = rhs` of a constant (built-in or user `hdef'`). -/
def defn (n : Name) : ProveM env (CertifiedThm env) := do
  let ctx ← read
  let rhs? :=
    match ctx.defs.find? (fun e => e.1 == n) with
    | some (_, ty, rhs) => some (ty, rhs)
    | none => builtinDef? n
  match rhs? with
  | some (ty, rhs) => ax (Tm.mkEq ty (.const n ty) rhs)
  | none => ProveM.throw s!"no definition for `{n}`"

end Hol
end Prove
end HOLean
