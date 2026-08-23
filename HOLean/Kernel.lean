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

`ABS` still needs `x ∉ FV(Γ)`.  Locally nameless syntax eliminates *binder*
clash (`Clash` during `INST_TYPE`), not hypothesis freshness.  `abstract`
binds the fvar `(x, α)` in the conclusion; hypotheses keep their fvars.
Without the side condition, `x = c ⊢ x = c` would yield
`x = c ⊢ (λy. y) = (λy. c)`.
-/

namespace HOLean

/-- Remove every copy of `p` (set difference on lists). -/
def hypsErase (p : Tm) (Γ : List Tm) : List Tm :=
  Γ.filter (· ≠ p)

theorem hypsErase_eq_of_not_mem {p : Tm} {Γ : List Tm} (h : p ∉ Γ) :
    hypsErase p Γ = Γ := by
  simp [hypsErase, List.filter_eq_self]
  intro x hx heq
  exact h (heq ▸ hx)

/-- The HOL Light primitive inference system, relative to an environment. -/
inductive Provable (env : Env) : List Tm → Tm → Prop where
  /-- `REFL t` gives `⊢ t = t`. -/
  | refl {t α} (ht : HasType env [] t α) :
      Provable env [] (Tm.mkEq α t t)
  /-- `TRANS`. -/
  | trans {Γ Δ s t u α}
      (h1 : Provable env Γ (Tm.mkEq α s t))
      (h2 : Provable env Δ (Tm.mkEq α t u)) :
      Provable env (Γ ++ Δ) (Tm.mkEq α s u)
  /-- `MK_COMB`. -/
  | mkComb {Γ Δ f g x y α β}
      (h1 : Provable env Γ (Tm.mkEq (α ↝ β) f g))
      (h2 : Provable env Δ (Tm.mkEq α x y)) :
      Provable env (Γ ++ Δ) (Tm.mkEq β (.app f x) (.app g y))
  /-- `ABS`: close a free variable `(x, α)` in both sides of an equation.
  Locally nameless syntax removes *binder* clash, but not this side
  condition: `abstract` binds `x` in the conclusion while hypotheses keep
  their fvars.  If `x` occurred in `Γ` one could turn `x = c ⊢ x = c` into
  `x = c ⊢ (λy. y) = (λy. c)`. -/
  | abs {Γ s t x α β}
      (h : Provable env Γ (Tm.mkEq β s t))
      (hfresh : ∀ p ∈ Γ, p.freeIn x α = false) :
      Provable env Γ (Tm.mkEq (α ↝ β) (s.abstract x α) (t.abstract x α))
  /-- `BETA`: the trivial redex `((λ x. t) x) = t[x]`. -/
  | beta {t x α β}
      (ht : HasType env [α] t β) :
      Provable env []
        (Tm.mkEq β (.app (.lam α t) (.fvar x α)) (t.open' (.fvar x α)))
  /-- `ASSUME`: a boolean term proves itself. -/
  | assume {p} (hp : HasType env [] p .bool) :
      Provable env [p] p
  /-- `EQ_MP`. -/
  | eqMp {Γ Δ p q}
      (h1 : Provable env Γ (Tm.mkEq .bool p q))
      (h2 : Provable env Δ p) :
      Provable env (Γ ++ Δ) q
  /-- `DEDUCT_ANTISYM_RULE`. -/
  | deductAntisym {Γ Δ p q}
      (h1 : Provable env Γ p)
      (h2 : Provable env Δ q) :
      Provable env (hypsErase q Γ ++ hypsErase p Δ) (Tm.mkEq .bool p q)
  /-- `INST_TYPE`. -/
  | instType {Γ p} (θ : TySubst) (h : Provable env Γ p) :
      Provable env (Γ.map (·.instTy θ)) (p.instTy θ)
  /-- `INST` (simultaneous, type-preserving substitution of free variables). -/
  | inst {Γ p σ} (hσ : σ.Ok env) (h : Provable env Γ p) :
      Provable env (Γ.map (·.applySubst σ)) (p.applySubst σ)
  /-- Admit one environment axiom, given that it is a closed boolean.
  In a well-formed environment this typing is `env.WF`; see `of_axiom`.
  Definitions are axioms `⊢ c = t`; the HOL schemas live in `holEnv`. -/
  | ax {p} (hp : env.axioms p) (hty : HasType env [] p .bool) :
      Provable env [] p

scoped notation:50 Γ:51 " ⊩[" env:0 "] " p:50 => Provable env Γ p

namespace Provable

variable {env : Env}

private theorem hyps_append {Γ Δ : List Tm}
    (hΓ : ∀ q ∈ Γ, HasType env [] q .bool)
    (hΔ : ∀ q ∈ Δ, HasType env [] q .bool) :
    ∀ q ∈ Γ ++ Δ, HasType env [] q .bool := by
  intro q hq
  match List.mem_append.1 hq with
  | Or.inl h => exact hΓ q h
  | Or.inr h => exact hΔ q h

/-- Growing the environment preserves kernel theorems. -/
theorem weakenEnv {env env' : Env} {Γ p}
    (hle : env.LE env') (h : Provable env Γ p) :
    Provable env' Γ p := by
  induction h with
  | refl ht => exact refl (ht.weakenEnv hle)
  | trans _ _ ih1 ih2 => exact trans ih1 ih2
  | mkComb _ _ ih1 ih2 => exact mkComb ih1 ih2
  | abs _ hfresh ih => exact abs ih hfresh
  | beta ht => exact beta (ht.weakenEnv hle)
  | assume hp => exact assume (hp.weakenEnv hle)
  | eqMp _ _ ih1 ih2 => exact eqMp ih1 ih2
  | deductAntisym _ _ ih1 ih2 => exact deductAntisym ih1 ih2
  | instType θ _ ih => exact instType θ ih
  | inst hσ _ ih => exact inst (hσ.weakenEnv hle) ih
  | ax hp hty => exact ax (hle.axioms _ hp) (hty.weakenEnv hle)

/-- Every hypothesis and the conclusion of a kernel theorem is a closed
boolean.  This is the first sanity theorem for the inference system. -/
theorem bool_typed [Env.HasEq env] {Γ p} (h : Γ ⊩[env] p) :
    (∀ q ∈ Γ, HasType env [] q .bool) ∧ HasType env [] p .bool := by
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
  | ax _ hty =>
    constructor
    · intro q hq; cases hq
    · exact hty

/-- Admit an axiom of a well-formed environment. -/
theorem of_axiom {p} (hwf : env.WF) (hp : env.axioms p) : [] ⊩[env] p :=
  ax hp (hwf.typed hp)

theorem concl_bool [Env.HasEq env] {Γ p} (h : Γ ⊩[env] p) : HasType env [] p .bool :=
  (bool_typed h).2

theorem hyps_bool [Env.HasEq env] {Γ p} (h : Γ ⊩[env] p) : ∀ q ∈ Γ, HasType env [] q .bool :=
  (bool_typed h).1

/-- Boolean reflexivity is also derivable from `ASSUME` + `DEDUCT_ANTISYM`. -/
theorem bool_refl [Env.HasEq env] {p} (hp : HasType env [] p .bool) :
    [] ⊩[env] Tm.mkEq .bool p p := by
  simpa [hypsErase] using Provable.deductAntisym (assume hp) (assume hp)

end Provable

end HOLean
