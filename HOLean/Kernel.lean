/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Typing

/-!
# The HOL Light kernel

Ten primitive inference rules, stated as an inductive predicate `Provable`.
Hypotheses are lists treated as finite sets (order and duplicates are
immaterial for validity).  See Harrison, *HOL Light: A Tutorial Introduction*,
and `fusion.ml` in the HOL Light distribution.

```
REFL                 ⊢ t = t
TRANS                Γ ⊢ s = t    Δ ⊢ t = u          ⇒  Γ,Δ ⊢ s = u
MK_COMB              Γ ⊢ f = g    Δ ⊢ x = y          ⇒  Γ,Δ ⊢ f x = g y
ABS (x ∉ FV(Γ))      Γ ⊢ s = t                       ⇒  Γ ⊢ (λx. s) = (λx. t)
BETA                 ⊢ ((λx. t) x) = t
ASSUME (p : bool)    {p} ⊢ p
EQ_MP                Γ ⊢ p = q    Δ ⊢ p              ⇒  Γ,Δ ⊢ q
DEDUCT_ANTISYM       Γ ⊢ p        Δ ⊢ q              ⇒  Γ\{q}, Δ\{p} ⊢ p = q
INST_TYPE θ          Γ ⊢ p                           ⇒  Γ[θ] ⊢ p[θ]
INST σ               Γ ⊢ p                           ⇒  Γ[σ] ⊢ p[σ]
```
-/

namespace HOLean

/-- Remove every copy of `p` (set difference on lists). -/
def hypsErase (p : Tm) (Γ : List Tm) : List Tm :=
  Γ.filter (· ≠ p)

/-- The HOL Light primitive inference system. -/
inductive Provable : List Tm → Tm → Prop where
  /-- `REFL t` gives `⊢ t = t`. -/
  | refl {t α} (ht : HasType [] t α) :
      Provable [] (Tm.mkEq α t t)
  /-- `TRANS`. -/
  | trans {Γ Δ s t u α}
      (h1 : Provable Γ (Tm.mkEq α s t))
      (h2 : Provable Δ (Tm.mkEq α t u)) :
      Provable (Γ ++ Δ) (Tm.mkEq α s u)
  /-- `MK_COMB`. -/
  | mkComb {Γ Δ f g x y α β}
      (h1 : Provable Γ (Tm.mkEq (α ↝ β) f g))
      (h2 : Provable Δ (Tm.mkEq α x y)) :
      Provable (Γ ++ Δ) (Tm.mkEq β (.app f x) (.app g y))
  /-- `ABS`: abstract a free variable that does not occur in the hypotheses. -/
  | abs {Γ s t x α β}
      (h : Provable Γ (Tm.mkEq β s t))
      (hfresh : ∀ p ∈ Γ, p.freeIn x α = false) :
      Provable Γ (Tm.mkEq (α ↝ β) (s.abstract x α) (t.abstract x α))
  /-- `BETA`: the trivial redex `((λ x. t) x) = t[x]`. -/
  | beta {t x α β}
      (ht : HasType [α] t β) :
      Provable []
        (Tm.mkEq β (.app (.lam α t) (.fvar x α)) (t.open' (.fvar x α)))
  /-- `ASSUME`: a boolean term proves itself. -/
  | assume {p} (hp : HasType [] p .bool) :
      Provable [p] p
  /-- `EQ_MP`. -/
  | eqMp {Γ Δ p q}
      (h1 : Provable Γ (Tm.mkEq .bool p q))
      (h2 : Provable Δ p) :
      Provable (Γ ++ Δ) q
  /-- `DEDUCT_ANTISYM_RULE`. -/
  | deductAntisym {Γ Δ p q}
      (h1 : Provable Γ p)
      (h2 : Provable Δ q) :
      Provable (hypsErase q Γ ++ hypsErase p Δ) (Tm.mkEq .bool p q)
  /-- `INST_TYPE`. -/
  | instType {Γ p} (θ : TySubst) (h : Provable Γ p) :
      Provable (Γ.map (·.instTy θ)) (p.instTy θ)
  /-- `INST` (simultaneous, type-preserving substitution of free variables). -/
  | inst {Γ p σ} (hσ : σ.Ok) (h : Provable Γ p) :
      Provable (Γ.map (·.applySubst σ)) (p.applySubst σ)

scoped notation:50 Γ:51 " ⊩ " p:50 => Provable Γ p

namespace Provable

private theorem hyps_append {Γ Δ : List Tm}
    (hΓ : ∀ q ∈ Γ, HasType [] q .bool)
    (hΔ : ∀ q ∈ Δ, HasType [] q .bool) :
    ∀ q ∈ Γ ++ Δ, HasType [] q .bool := by
  intro q hq
  match List.mem_append.1 hq with
  | Or.inl h => exact hΓ q h
  | Or.inr h => exact hΔ q h

/-- Every hypothesis and the conclusion of a kernel theorem is a closed
boolean.  This is the first sanity theorem for the inference system. -/
theorem bool_typed {Γ p} (h : Γ ⊩ p) :
    (∀ q ∈ Γ, HasType [] q .bool) ∧ HasType [] p .bool := by
  induction h with
  | refl ht =>
    constructor
    · intro q hq; cases hq
    · exact HasType.mkEq ht ht
  | trans _h1 _h2 ih1 ih2 =>
    refine And.intro (hyps_append ih1.1 ih2.1) ?_
    obtain ⟨_, hs, _ht⟩ := HasType.dest_mkEq ih1.2
    obtain ⟨_, _ht', hu⟩ := HasType.dest_mkEq ih2.2
    exact HasType.mkEq hs hu
  | mkComb _h1 _h2 ih1 ih2 =>
    refine And.intro (hyps_append ih1.1 ih2.1) ?_
    obtain ⟨_, hf, hg⟩ := HasType.dest_mkEq ih1.2
    obtain ⟨_, hx, hy⟩ := HasType.dest_mkEq ih2.2
    exact HasType.mkEq (HasType.app hf hx) (HasType.app hg hy)
  | abs _h _hfresh ih =>
    obtain ⟨_, hs, ht⟩ := HasType.dest_mkEq ih.2
    exact ⟨ih.1, HasType.mkEq hs.abstract ht.abstract⟩
  | beta ht =>
    rename_i t x α β
    refine And.intro (by intro q hq; cases hq) ?_
    exact HasType.mkEq
      (HasType.app (HasType.lam ht) (HasType.fvar x α))
      (ht.open' (HasType.fvar x α))
  | assume hp =>
    refine And.intro ?_ hp
    intro q hq
    simp at hq
    subst hq
    exact hp
  | eqMp _h1 _h2 ih1 ih2 =>
    refine And.intro (hyps_append ih1.1 ih2.1) ?_
    obtain ⟨_, _hp, hq⟩ := HasType.dest_mkEq ih1.2
    exact hq
  | deductAntisym _h1 _h2 ih1 ih2 =>
    rename_i Γ Δ p q
    refine And.intro ?_ (HasType.mkEq ih1.2 ih2.2)
    intro r hr
    match List.mem_append.1 hr with
    | Or.inl hmem =>
      have : r ∈ Γ ∧ r ≠ q := by simpa [hypsErase] using hmem
      exact ih1.1 r this.1
    | Or.inr hmem =>
      have : r ∈ Δ ∧ r ≠ p := by simpa [hypsErase] using hmem
      exact ih2.1 r this.1
  | instType θ _h ih =>
    refine And.intro ?_ ?_
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      simpa [Ty.inst_bool] using (ih.1 q' hq').instTy θ
    · simpa [Ty.inst_bool] using ih.2.instTy θ
  | inst hσ _h ih =>
    refine And.intro ?_ ?_
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact (ih.1 q' hq').applySubst hσ
    · exact ih.2.applySubst hσ

theorem concl_bool {Γ p} (h : Γ ⊩ p) : HasType [] p .bool :=
  (bool_typed h).2

theorem hyps_bool {Γ p} (h : Γ ⊩ p) : ∀ q ∈ Γ, HasType [] q .bool :=
  (bool_typed h).1

/-- Boolean reflexivity is also derivable from `ASSUME` + `DEDUCT_ANTISYM`. -/
theorem bool_refl {p} (hp : HasType [] p .bool) : [] ⊩ Tm.mkEq .bool p p := by
  simpa [hypsErase] using Provable.deductAntisym (assume hp) (assume hp)

end Provable

end HOLean
