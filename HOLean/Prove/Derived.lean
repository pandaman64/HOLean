/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Prove.Logic

/-!
# Packaging: axioms, `closeTheorem`

SYM / DISCH / GEN / SPEC / connective rules live in `Conv` and `Logic` as
`ProveM` programs.  This file keeps `closeTheorem` and the three HOL axioms.
-/

namespace HOLean
namespace Prove
namespace Hol

variable {env : Env}

/-- One η instance: `⊢ (λ x. f x) = f`. -/
def eta (α β : Ty) (f : Tm) : ProveM env (CertifiedThm env) := do
  let ⟨τ, _⟩ ← infer [] f
  if _hτ : τ = α ↝ β then
    let th0 ← ax etaAxiom
    let θ : TySubst := [(primTyVar, α), (primTyVarB, β)]
    let th1 ← instType θ th0
    spec f th1
  else
    ProveM.throw s!"ETA: expected type {repr (α ↝ β)}, got {repr τ}"

/-- One SELECT instance: `⊢ P x ⇒ P (ε P)`. -/
def select (α : Ty) (P x : Tm) : ProveM env (CertifiedThm env) := do
  let ⟨τP, _⟩ ← infer [] P
  let ⟨τx, _⟩ ← infer [] x
  if _hP : τP = α ↝ .bool then
    if _hx : τx = α then
      let th0 ← ax selectAxiom
      let θ : TySubst := [(primTyVar, α)]
      let th1 ← instType θ th0
      let th2 ← spec P th1
      spec x th2
    else ProveM.throw s!"SELECT: witness has type {repr τx}"
  else ProveM.throw s!"SELECT: predicate has type {repr τP}"

/-- The infinity axiom. -/
def infinity : ProveM env (CertifiedThm env) :=
  ax infinityAxiom

/-- Require a closed theorem of the expected sentence. -/
def assertClosed (stmt : Tm) (ct : CertifiedThm env) :
    ProveM env (Proof (Provable env [] stmt)) :=
  if hΓ : ct.hyps = [] then
    if hc : ct.concl = stmt then
      have pΓ : Provable env [] ct.concl := hΓ ▸ ct.proof
      return ⟨hc ▸ pΓ⟩
    else ProveM.throw s!"proved {repr ct.concl}, expected {repr stmt}"
  else ProveM.throw s!"theorem still has hypotheses {repr ct.hyps}"

/-- Discharge telescope hypotheses and generalize parameters, then
check the closed statement. -/
def closeTheorem (stmt concl : Tm) (hyps : List Tm) (params : List (Name × Ty))
    (m : ProveM env (CertifiedThm env)) :
    ProveM env (Proof (Provable env [] stmt)) := do
  let mut ct ← m
  if ct.hyps.isEmpty && ct.concl == stmt then
    assertClosed stmt ct
  else if ct.concl == concl then
    for p in hyps.reverse do
      ct ← disch p ct
    for (n, α) in params.reverse do
      ct ← gen n α ct
    assertClosed stmt ct
  else
    ProveM.throw s!"proved {repr ct.concl}, expected {repr concl} or {repr stmt}"

end Hol
end Prove
end HOLean
