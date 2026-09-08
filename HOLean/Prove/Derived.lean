/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Derived
import HOLean.Prove.Kernel

/-!
# Derived LCF combinators

SYM, `⊢ T`, DISCH, GEN, SPEC, axioms, and `closeTheorem`.
-/

namespace HOLean
namespace Prove
namespace Hol

variable {env : Env}

/-- `Γ ⊢ s = t` implies `Γ ⊢ t = s`. -/
def sym (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  ProveM.withConn do
    match h1 : Tm.destEq th.concl with
    | some (α, s, t) =>
      return mk th.hyps (Tm.mkEq α t s) (by
        have e1 := Tm.destEq_eq h1
        have p1 : Provable env th.hyps (Tm.mkEq α s t) := e1 ▸ th.proof
        exact Provable.eq_sym p1)
    | none => ProveM.throw "SYM: expected an equation"

/-- `⊢ T`. -/
def truth : ProveM env (CertifiedThm env) :=
  ProveM.withConn do
    return mk [] Tm.tru Provable.tru_intro

/-- A name used as the combinator variable in `DISCH`. -/
def freshDischName : Name := "_disch"

/-- `DISCH p`: from `Γ ⊢ q` conclude `Γ \ {p} ⊢ p ⇒ q`.

Follows HOL Light `bool.ml`: `CONJ (ASSUME p) th`, left projection of
`ASSUME (p ∧ q)`, `DEDUCT_ANTISYM`, then the definition of `⇒`. -/
def disch (p : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  ProveM.withConn do
    let ⟨hp⟩ ← checkBool [] p
    let q := th.concl
    let hq := Provable.concl_bool th.proof
    let x := freshDischName
    if hxp : p.freeIn x Tm.boolCombTy = false then
      if hxq : q.freeIn x Tm.boolCombTy = false then
        if hxpB : p.freeIn x .bool = false then
          let ⟨hTΔ⟩ ← checkNotMem Tm.tru th.hyps
          let ⟨hTp⟩ ← checkNotMem Tm.tru [p]
          let ⟨hxΔ⟩ ← checkFreshHyps x Tm.boolCombTy th.hyps
          let ⟨hxP⟩ ← checkFreshHyps x Tm.boolCombTy [p]
          let th1 := Provable.conj (Γ := [p]) (Δ := th.hyps) x
            (Provable.assume hp) th.proof hTp hTΔ hxP hxΔ hxp hxq hxpB
          let handTy : HasType env [] (p.and q) .bool := HasType.and hp hq
          let th2 := Provable.and_elim_left (Γ := [p.and q]) x
            (Provable.assume handTy) hp hq hxp hxq hxpB
          let th3 := Provable.deductAntisym th1 th2
          let hunf := Provable.imp_eq_expand (p := p) (q := q) x hp hq hxpB
          return mk (hypsErase p th.hyps) (Tm.imp p q) (by
            have pf := Provable.eqMp (Provable.eq_sym hunf) th3
            simpa [hypsErase, Tm.impExpand, q] using pf)
        else
          ProveM.throw "DISCH: combinator variable `_disch` is free in the terms"
      else
        ProveM.throw "DISCH: combinator variable `_disch` is free in the terms"
    else
      ProveM.throw "DISCH: combinator variable `_disch` is free in the terms"

/-- Generalize: from `Γ ⊢ t` with `x` not free in `Γ`, conclude `Γ ⊢ ∀ x. t`. -/
def gen (x : Name) (α : Ty) (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  ProveM.withConn do
    let ⟨hfresh⟩ ← checkFreshHyps x α th.hyps
    let ⟨hT⟩ ← checkNotMem Tm.tru th.hyps
    let ⟨_⟩ ← checkBool [] th.concl
    return mk th.hyps (Tm.all α (th.concl.abstract x α))
      (Provable.gen th.proof hT hfresh)

/-- A name reserved for `SPEC` β-conversion. -/
def freshSpecName : Name := "_spec"

/-- `SPEC`: from `Γ ⊢ ∀ (λ x. body)` conclude `Γ ⊢ body[t]`, or `Γ ⊢ P t`. -/
def spec (t : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  ProveM.withConn do
    match hconcl : th.concl with
    | .app (.const n ((.arrow α .bool) ↝ .bool)) (.lam β body) =>
      if hn : n = allName then
        if hβ : β = α then
          let ⟨ht⟩ ← checkType [] t α
          let ⟨hbody⟩ ← checkBool [α] body
          let x := freshSpecName
          if hf : body.freeIn x α = false then
            return mk th.hyps (body.open' t)
              (Provable.spec_beta (Γ := th.hyps) (body := body) (t := t) (α := α) x
                (by
                  have : th.concl = Tm.all α (.lam α body) := by
                    subst hn; subst hβ; simpa [Tm.all] using hconcl
                  exact this ▸ th.proof)
                hbody ht hf)
          else
            ProveM.throw s!"SPEC: `{x}` is free in the body"
        else ProveM.throw s!"SPEC: binder type {repr β} ≠ domain {repr α}"
      else ProveM.throw "SPEC: expected a universal quantifier"
    | .app (.const n ((.arrow α .bool) ↝ .bool)) P =>
      if hn : n = allName then
        let ⟨hP⟩ ← checkType [] P (α ↝ .bool)
        let ⟨ht⟩ ← checkType [] t α
        let x := freshSpecName
        return mk th.hyps (P.app t)
          (Provable.spec (Γ := th.hyps) (P := P) (t := t) (α := α) x
            (by
              have : th.concl = Tm.all α P := by
                subst hn; simpa [Tm.all] using hconcl
              exact this ▸ th.proof)
            hP ht)
      else ProveM.throw "SPEC: expected a universal quantifier"
    | _ => ProveM.throw "SPEC: expected `∀ P`"

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
