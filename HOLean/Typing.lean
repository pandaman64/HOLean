/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Tm

/-!
# Extrinsic typing

`HasType Γ t α` means `t` has type `α` when bound indices are interpreted in
the context `Γ` (innermost binder first).  Free variables carry their own
types, so they need no context entry.

A term that is well-typed in the empty bound context is locally closed: there
is no constructor for an out-of-scope `bvar`.
-/

namespace HOLean

/-- Algorithmic type inference. -/
def Tm.infer (Γ : List Ty) : Tm → Option Ty
  | bvar i => Ctx.get Γ i
  | fvar _ α => some α
  | const c α => some (c.inst α)
  | app f a =>
    match f.infer Γ, a.infer Γ with
    | some (α ↝ β), some α' => if α = α' then some β else none
    | _, _ => none
  | lam α t =>
    match t.infer (α :: Γ) with
    | some β => some (α ↝ β)
    | none => none

/-- Declarative typing judgment. -/
inductive HasType : List Ty → Tm → Ty → Prop where
  | bvar {Γ i α} (h : Ctx.get Γ i = some α) :
      HasType Γ (.bvar i) α
  | fvar {Γ x α} :
      HasType Γ (.fvar x α) α
  | const {Γ c α} :
      HasType Γ (.const c α) (c.inst α)
  | app {Γ f a α β} :
      HasType Γ f (α ↝ β) → HasType Γ a α → HasType Γ (.app f a) β
  | lam {Γ t α β} :
      HasType (α :: Γ) t β → HasType Γ (.lam α t) (α ↝ β)

/-- Unique typing: a term has at most one type in a given context. -/
theorem HasType.unique {Γ t α} (h : HasType Γ t α) :
    ∀ {β}, HasType Γ t β → α = β := by
  induction h with
  | bvar hi =>
    intro β hβ
    cases hβ with
    | bvar hi' => exact Ctx.get_eq_some_unique hi hi'
  | fvar =>
    intro β hβ
    cases hβ
    rfl
  | const =>
    intro β hβ
    cases hβ
    rfl
  | app _ _ ihf iha =>
    intro γ hγ
    cases hγ with
    | app hf' ha' =>
      have hfEq := ihf hf'
      injection hfEq with hα hβ
      have haEq := iha (hα ▸ ha')
      exact hβ
  | lam _ ih =>
    intro γ hγ
    cases hγ with
    | lam ht' =>
      cases ih ht'
      rfl

theorem HasType.infer_of {Γ t α} (h : HasType Γ t α) : t.infer Γ = some α := by
  induction h with
  | bvar hi =>
    simpa [Tm.infer] using hi
  | fvar =>
    simp [Tm.infer]
  | const =>
    simp [Tm.infer]
  | app hf ha ihf iha =>
    simp [Tm.infer, ihf, iha]
  | lam ht ih =>
    simp [Tm.infer, ih]

theorem HasType.of_infer {Γ : List Ty} :
    ∀ {t α}, t.infer Γ = some α → HasType Γ t α := by
  intro t
  induction t generalizing Γ with
  | bvar i =>
    intro α h
    exact HasType.bvar (by simpa [Tm.infer] using h)
  | fvar x β =>
    intro α h
    have : α = β := by simpa [Tm.infer] using h
    exact this ▸ HasType.fvar
  | const c β =>
    intro α h
    have : α = c.inst β := by simpa [Tm.infer] using h
    exact this ▸ HasType.const
  | app f a ihf iha =>
    intro α h
    cases hf : f.infer Γ with
    | none =>
      simp [Tm.infer, hf] at h
    | some σ =>
      cases ha : a.infer Γ with
      | none =>
        simp [Tm.infer, hf, ha] at h
      | some τ =>
        cases σ with
        | arrow γ β =>
          simp [Tm.infer, hf, ha] at h
          split_ifs at h with hγ
          · cases h
            exact HasType.app (ihf hf) (hγ ▸ iha ha)
          · cases h
        | var _ => simp [Tm.infer, hf, ha] at h
        | bool => simp [Tm.infer, hf, ha] at h
        | ind => simp [Tm.infer, hf, ha] at h
  | lam β t iht =>
    intro α h
    cases ht : t.infer (β :: Γ) with
    | none =>
      simp [Tm.infer, ht] at h
    | some γ =>
      simp [Tm.infer, ht] at h
      cases h
      exact HasType.lam (iht ht)

/-- Typing is decidable via inference. -/
theorem HasType.iff_infer {Γ t α} : HasType Γ t α ↔ t.infer Γ = some α :=
  ⟨HasType.infer_of, HasType.of_infer⟩

/-- Binders may be added *outside* the current context (higher indices). -/
theorem HasType.weaken {Γ Δ t α} (h : HasType Γ t α) :
    HasType (Γ ++ Δ) t α := by
  induction h with
  | bvar hi =>
    exact HasType.bvar (Ctx.get_append_left hi)
  | fvar =>
    exact HasType.fvar
  | const =>
    exact HasType.const
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- A term typed in the empty bound context remains typed in any context. -/
theorem HasType.of_closed {Γ t α} (h : HasType [] t α) : HasType Γ t α := by
  simpa using h.weaken (Δ := Γ)

/-- Type instantiation preserves typing. -/
theorem HasType.instTy {Γ t α} (h : HasType Γ t α) (θ : TySubst) :
    HasType (Γ.map (Ty.inst θ)) (t.instTy θ) (α.inst θ) := by
  induction h with
  | bvar hi =>
    exact HasType.bvar (by simpa [Ctx.get_map] using congrArg (Option.map (Ty.inst θ)) hi)
  | fvar =>
    exact HasType.fvar
  | const c α =>
    simpa [Const.inst_tyInst] using
      (HasType.const (Γ := Γ.map (Ty.inst θ)) (c := c) (α := α.inst θ))
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- Single free-variable substitution preserves typing when the substitute is
closed of the expected type. -/
theorem HasType.substFvar {Γ t β x α u}
    (ht : HasType Γ t β) (hu : HasType [] u α) :
    HasType Γ (t.substFvar x α u) β := by
  induction ht with
  | bvar hi =>
    exact HasType.bvar hi
  | fvar y γ =>
    by_cases h : y = x ∧ γ = α
    · have hγ : γ = α := h.2
      simp [Tm.substFvar, h]
      exact hγ ▸ hu.of_closed
    · simp [Tm.substFvar, h]
      exact HasType.fvar
  | const =>
    exact HasType.const
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- A simultaneous substitution is type-correct when every replacement is a
closed term of the advertised type. -/
def Tm.Subst.Ok (σ : Tm.Subst) : Prop :=
  ∀ x α u, σ.lookup x α = some u → HasType [] u α

theorem HasType.applySubst {Γ t β σ} (ht : HasType Γ t β) (hσ : σ.Ok) :
    HasType Γ (t.applySubst σ) β := by
  induction ht with
  | bvar hi =>
    exact HasType.bvar hi
  | fvar x α =>
    cases hlook : σ.lookup x α with
    | none =>
      simp [Tm.applySubst, hlook]
      exact HasType.fvar
    | some u =>
      simp [Tm.applySubst, hlook]
      exact (hσ x α u hlook).of_closed
  | const =>
    simp [Tm.applySubst]
    exact HasType.const
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- Closing a free variable introduces a binder of that variable's type. -/
theorem HasType.closeAt {Γ t β x α} (ht : HasType Γ t β) :
    HasType (Γ ++ [α]) (t.closeAt Γ.length x α) β := by
  induction ht with
  | bvar i hi =>
    exact HasType.bvar (Ctx.get_append_left hi)
  | fvar y γ =>
    by_cases h : y = x ∧ γ = α
    · have hγ : γ = α := h.2
      simp [Tm.closeAt, h]
      apply HasType.bvar
      -- `bvar Γ.length` looks up the newly appended `α`
      have : Ctx.get (Γ ++ [α]) Γ.length = some α := by
        clear ht h hγ y
        induction Γ with
        | nil => simp
        | cons _ Γ ih =>
          simpa [List.length] using ih
      exact hγ ▸ this
    · simp [Tm.closeAt, h]
      exact HasType.fvar
  | const =>
    exact HasType.const
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam δ t β ih =>
    -- IH: HasType ((δ :: Γ) ++ [α]) (t.closeAt (δ :: Γ).length x α) β
    simpa [Tm.closeAt, List.length] using HasType.lam ih

theorem HasType.close {t β x α} (ht : HasType [] t β) :
    HasType [α] (t.close x α) β := by
  simpa [Tm.close] using ht.closeAt (Γ := []) (x := x) (α := α)

theorem HasType.abstract {t β x α} (ht : HasType [] t β) :
    HasType [] (t.abstract x α) (α ↝ β) :=
  HasType.lam (ht.close (x := x) (α := α))

/-- Opening the outermost extra binder at a closed term of that binder's type. -/
theorem HasType.openAt_aux {α u} (hu : HasType [] u α) :
    ∀ {Γ t β} (ht : HasType Γ t β) (Δ : List Ty),
      Γ = Δ ++ [α] → HasType Δ (t.openAt Δ.length u) β := by
  intro Γ t β ht
  induction ht with
  | bvar i hi =>
    intro Δ hΓ
    subst hΓ
    rw [Ctx.get_snoc] at hi
    by_cases hlen : i = Δ.length
    · simp [hlen] at hi
      cases hi
      simp [Tm.openAt, hlen]
      exact hu.of_closed
    · simp [hlen] at hi
      simp [Tm.openAt, hlen]
      exact HasType.bvar hi
  | fvar =>
    intro Δ hΓ
    subst hΓ
    simp [Tm.openAt]
    exact HasType.fvar
  | const =>
    intro Δ hΓ
    subst hΓ
    simp [Tm.openAt]
    exact HasType.const
  | app _ _ ihf iha =>
    intro Δ hΓ
    exact HasType.app (ihf Δ hΓ) (iha Δ hΓ)
  | lam δ _ _ ih =>
    intro Δ hΓ
    subst hΓ
    refine HasType.lam (ih (δ :: Δ) ?_)
    simp [Tm.openAt, List.length]

theorem HasType.openAt {Γ t β α u} (ht : HasType (Γ ++ [α]) t β)
    (hu : HasType [] u α) :
    HasType Γ (t.openAt Γ.length u) β :=
  HasType.openAt_aux hu ht Γ rfl

theorem HasType.open' {t β α u} (ht : HasType [α] t β) (hu : HasType [] u α) :
    HasType [] (t.open' u) β := by
  simpa [Tm.open'] using ht.openAt (Γ := []) (α := α) hu

/-- Equations are booleans when both sides share a type. -/
theorem HasType.mkEq {Γ s t α} (hs : HasType Γ s α) (ht : HasType Γ t α) :
    HasType Γ (Tm.mkEq α s t) .bool :=
  HasType.app (HasType.app HasType.const hs) ht

/-- Inversion for `s = t`. -/
theorem HasType.dest_mkEq {Γ s t α β} (h : HasType Γ (Tm.mkEq α s t) β) :
    β = .bool ∧ HasType Γ s α ∧ HasType Γ t α := by
  cases h with
  | app hf ht =>
    cases hf with
    | app hc hs =>
      cases hc
      exact ⟨rfl, hs, ht⟩

end HOLean
