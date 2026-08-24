/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Env
import Init.Data.List.Nat.InsertIdx

/-!
# Extrinsic typing

`HasType env Γ t α` means `t` has type `α` in environment `env` when bound
indices are interpreted in the context `Γ` (innermost binder first).  Free
variables carry their own types, so they need no context entry.

A constant `const n inst` is well-typed when `env` assigns `n` a generic
type of which `inst` is an instance.  Typing reads only `env.constants`.

A term that is well-typed in the empty bound context is automatically locally
closed: there is no way to type an unbound `bvar`.
-/

namespace HOLean

/-- Algorithmic type inference, relative to an environment. -/
def Tm.infer (env : Env) (t : Tm) (Γ : List Ty) : Option Ty :=
  match t with
  | bvar i => Γ[i]?
  | fvar _ α => some α
  | const n τ =>
    match env.constants n with
    | some gen => if (gen.matchTy τ []).isSome then some τ else none
    | none => none
  | app f a =>
    match f.infer env Γ, a.infer env Γ with
    | some (α ↝ β), some α' => if α = α' then some β else none
    | _, _ => none
  | lam α t =>
    match t.infer env (α :: Γ) with
    | some β => some (α ↝ β)
    | none => none

/-- Declarative typing judgment, relative to an environment. -/
inductive HasType (env : Env) : List Ty → Tm → Ty → Prop where
  | bvar {Γ α} {i : Nat} (h : Γ[i]? = some α) :
      HasType env Γ (.bvar i) α
  | fvar {Γ} (x : Name) (α : Ty) :
      HasType env Γ (.fvar x α) α
  | const {Γ n inst gen}
      (hconst : env.constants n = some gen)
      (hinst : gen.isInstanceOf inst) :
      HasType env Γ (.const n inst) inst
  | app {Γ α β} {f a : Tm}
      (hf : HasType env Γ f (α ↝ β)) (ha : HasType env Γ a α) :
      HasType env Γ (.app f a) β
  | lam {Γ α β} {t : Tm}
      (ht : HasType env (α :: Γ) t β) :
      HasType env Γ (.lam α t) (α ↝ β)

variable {env : Env}

/-- Unique typing: a term has at most one type in a given context. -/
theorem HasType.unique {Γ t α} (h : HasType env Γ t α) :
    ∀ {β}, HasType env Γ t β → α = β := by
  induction h with
  | bvar hi =>
    intro β hβ
    cases hβ with
    | bvar hi' => exact Option.some.inj (hi.symm.trans hi')
  | fvar x α =>
    intro β hβ
    cases hβ
    rfl
  | const hconst hinst =>
    intro β hβ
    cases hβ
    rfl
  | app _ _ ihf _iha =>
    intro γ hγ
    cases hγ with
    | app hf' _ha' =>
      injection ihf hf'
  | lam _ ih =>
    intro γ hγ
    cases hγ with
    | lam ht' =>
      cases ih ht'
      rfl

theorem HasType.infer_of {Γ t α} (h : HasType env Γ t α) : t.infer env Γ = some α := by
  induction h with
  | bvar hi =>
    simpa [Tm.infer] using hi
  | fvar x α =>
    simp [Tm.infer]
  | const hconst hinst =>
    simp [Tm.infer, hconst, Ty.matchTy_of_isInstanceOf hinst]
  | app _ _ ihf iha =>
    simp [Tm.infer, ihf, iha]
  | lam _ ih =>
    simp [Tm.infer, ih]

theorem HasType.of_infer {Γ : List Ty} :
    ∀ {t α}, t.infer env Γ = some α → HasType env Γ t α := by
  intro t
  induction t generalizing Γ with
  | bvar i =>
    intro α h
    exact HasType.bvar (by simpa [Tm.infer] using h)
  | fvar x β =>
    intro α h
    simp [Tm.infer] at h
    exact h ▸ HasType.fvar x β
  | const n β =>
    intro α h
    cases hc : env.constants n with
    | none =>
      simp [Tm.infer, hc] at h
    | some gen =>
      simp [Tm.infer, hc] at h
      by_cases hm : (gen.matchTy β []).isSome
      · simp [hm] at h
        cases h
        exact HasType.const hc (Ty.isInstanceOf_of_isSome (by simp [hm]))
      · simp [hm] at h
  | app f a ihf iha =>
    intro α h
    cases hf : f.infer env Γ with
    | none =>
      simp [Tm.infer, hf] at h
    | some σ =>
      cases ha : a.infer env Γ with
      | none =>
        simp [Tm.infer, hf, ha] at h
      | some τ =>
        cases σ with
        | arrow γ β =>
          simp [Tm.infer, hf, ha] at h
          obtain ⟨hγ, rfl⟩ := h
          exact HasType.app (ihf hf) (hγ ▸ iha ha)
        | var _ => simp [Tm.infer, hf, ha] at h
        | bool => simp [Tm.infer, hf, ha] at h
        | ind => simp [Tm.infer, hf, ha] at h
  | lam β t iht =>
    intro α h
    cases ht : t.infer env (β :: Γ) with
    | none =>
      simp [Tm.infer, ht] at h
    | some γ =>
      simp [Tm.infer, ht] at h
      cases h
      exact HasType.lam (iht ht)

/-- Typing is decidable via inference. -/
theorem HasType.iff_infer {Γ t α} : HasType env Γ t α ↔ t.infer env Γ = some α :=
  ⟨HasType.infer_of, HasType.of_infer⟩

/-- Binders may be added *outside* the current context (higher indices). -/
theorem HasType.weaken {Γ Δ t α} (h : HasType env Γ t α) :
    HasType env (Γ ++ Δ) t α := by
  induction h with
  | bvar hi =>
    exact HasType.bvar <|
      (List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1).trans hi
  | fvar x α =>
    exact HasType.fvar x α
  | const hconst hinst =>
    exact HasType.const hconst hinst
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- Growing the environment preserves typing. -/
theorem HasType.weakenEnv {env' : Env} {Γ t α}
    (hle : env.LE env') (h : HasType env Γ t α) :
    HasType env' Γ t α := by
  induction h with
  | bvar hi =>
    exact HasType.bvar hi
  | fvar x α =>
    exact HasType.fvar x α
  | const hconst hinst =>
    exact HasType.const (hle.constants _ _ hconst) hinst
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- A term typed in the empty bound context remains typed in any context. -/
theorem HasType.of_closed {Γ t α} (h : HasType env [] t α) : HasType env Γ t α := by
  simpa using (HasType.weaken (Γ := []) (Δ := Γ) h)

/-- Drop unused *outer* binders when the term does not mention them. -/
theorem HasType.strengthen :
    ∀ {t : Tm} {Δ Γ : List Ty} {α},
      HasType env (Δ ++ Γ) t α → t.LC Δ.length = true → HasType env Δ t α := by
  intro t
  induction t with
  | bvar i =>
    intro Δ Γ α h hLC
    simp [Tm.LC] at hLC
    cases h with
    | bvar hi =>
      exact HasType.bvar ((List.getElem?_append_left hLC).symm.trans hi)
  | fvar x β =>
    intro Δ Γ α h hLC
    cases h
    exact HasType.fvar x β
  | const n β =>
    intro Δ Γ α h hLC
    cases h
    exact HasType.const ‹_› ‹_›
  | app f a ihf iha =>
    intro Δ Γ α h hLC
    simp [Tm.LC] at hLC
    cases h with
    | app hf ha =>
      exact HasType.app (ihf hf hLC.1) (iha ha hLC.2)
  | lam β t ih =>
    intro Δ Γ α h hLC
    simp [Tm.LC] at hLC
    cases h with
    | lam ht =>
      exact HasType.lam (ih (Δ := β :: Δ) (Γ := Γ) ht (by simpa [List.length] using hLC))

theorem HasType.strengthen_nil {Γ t α} (h : HasType env Γ t α) (hLC : t.LC 0 = true) :
    HasType env [] t α :=
  HasType.strengthen (Δ := []) (Γ := Γ) (by simpa using h) hLC

/-- Type instantiation preserves typing. -/
theorem HasType.instTy {Γ t α} (h : HasType env Γ t α) (θ : TySubst) :
    HasType env (Γ.map (Ty.inst θ)) (t.instTy θ) (α.inst θ) := by
  induction h with
  | bvar hi =>
    exact HasType.bvar (by simpa [List.getElem?_map] using congrArg (Option.map (Ty.inst θ)) hi)
  | fvar x α =>
    exact HasType.fvar x (α.inst θ)
  | const hconst hinst =>
    exact HasType.const hconst (hinst.inst θ)
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- Single free-variable substitution preserves typing when the substitute is
closed of the expected type. -/
theorem HasType.substFvar {Γ t β x α u}
    (ht : HasType env Γ t β) (hu : HasType env [] u α) :
    HasType env Γ (t.substFvar x α u) β := by
  induction ht with
  | bvar hi =>
    exact HasType.bvar hi
  | fvar y γ =>
    by_cases h : y = x ∧ γ = α
    · have hs : (Tm.fvar y γ).substFvar x α u = u := by simp [Tm.substFvar, h]
      rw [hs]
      exact h.2 ▸ hu.of_closed
    · have hs : (Tm.fvar y γ).substFvar x α u = Tm.fvar y γ := by
        simp [Tm.substFvar, h]
      rw [hs]
      exact HasType.fvar y γ
  | const hconst hinst =>
    exact HasType.const hconst hinst
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- A simultaneous substitution is type-correct when every replacement is a
closed term of the advertised type. -/
def Tm.Subst.Ok (env : Env) (σ : Tm.Subst) : Prop :=
  ∀ x α u, σ.lookup x α = some u → HasType env [] u α

theorem Tm.Subst.Ok.weakenEnv {env' : Env} {σ : Tm.Subst}
    (hle : env.LE env') (hσ : σ.Ok env) : σ.Ok env' :=
  fun x α u h => (hσ x α u h).weakenEnv hle

theorem HasType.applySubst {Γ t β σ} (ht : HasType env Γ t β) (hσ : σ.Ok env) :
    HasType env Γ (t.applySubst σ) β := by
  induction ht with
  | bvar hi =>
    exact HasType.bvar hi
  | fvar x α =>
    simp [Tm.applySubst]
    cases hlook : σ.lookup x α with
    | none =>
      exact HasType.fvar x α
    | some u =>
      exact (hσ x α u hlook).of_closed
  | const hconst hinst =>
    exact HasType.const hconst hinst
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    exact HasType.lam ih

/-- Closing a free variable introduces a binder of that variable's type. -/
theorem HasType.closeAt {Γ t β x α} (ht : HasType env Γ t β) :
    HasType env (Γ ++ [α]) (t.closeAt Γ.length x α) β := by
  induction ht with
  | bvar hi =>
    exact HasType.bvar <|
      (List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1).trans hi
  | fvar y γ =>
    rename_i Γ
    by_cases h : y = x ∧ γ = α
    · have hs : (Tm.fvar y γ).closeAt Γ.length x α = Tm.bvar Γ.length := by
        simp [Tm.closeAt, h]
      rw [hs]
      exact HasType.bvar (h.2 ▸ List.getElem?_concat_length (l := Γ) (a := α))
    · have hs : (Tm.fvar y γ).closeAt Γ.length x α = Tm.fvar y γ := by
        simp [Tm.closeAt, h]
      rw [hs]
      exact HasType.fvar y γ
  | const hconst hinst =>
    exact HasType.const hconst hinst
  | app _ _ ihf iha =>
    exact HasType.app ihf iha
  | lam _ ih =>
    simpa [Tm.closeAt, List.length] using HasType.lam ih

theorem HasType.close {t β x α} (ht : HasType env [] t β) :
    HasType env [α] (t.close x α) β := by
  simpa [Tm.close] using ht.closeAt (Γ := []) (x := x) (α := α)

theorem HasType.abstract {t β x α} (ht : HasType env [] t β) :
    HasType env [] (t.abstract x α) (α ↝ β) :=
  HasType.lam (ht.close (x := x) (α := α))

/-- Opening the outermost extra binder at a closed term of that binder's type. -/
theorem HasType.openAt_aux {α u} (hu : HasType env [] u α) :
    ∀ {Γ t β} (_h : HasType env Γ t β) (Δ : List Ty),
      Γ = Δ ++ [α] → HasType env Δ (t.openAt Δ.length u) β := by
  intro Γ t β h
  induction h with
  | bvar hi =>
    rename_i i
    intro Δ hΓ
    subst hΓ
    rw [List.getElem?_snoc] at hi
    by_cases hlen : i = Δ.length
    · simp [hlen] at hi
      cases hi
      simp [Tm.openAt, hlen]
      exact hu.of_closed
    · simp [hlen] at hi
      simp [Tm.openAt, hlen]
      exact HasType.bvar hi
  | fvar x α' =>
    intro Δ hΓ
    subst hΓ
    simp [Tm.openAt]
    exact HasType.fvar x α'
  | const hconst hinst =>
    intro Δ hΓ
    subst hΓ
    simp [Tm.openAt]
    exact HasType.const hconst hinst
  | app _ _ ihf iha =>
    intro Δ hΓ
    exact HasType.app (ihf Δ hΓ) (iha Δ hΓ)
  | lam _ht ih =>
    intro Δ hΓ
    subst hΓ
    apply HasType.lam
    apply ih
    simp [List.cons_append]

theorem HasType.openAt {Γ t β α u} (ht : HasType env (Γ ++ [α]) t β)
    (hu : HasType env [] u α) :
    HasType env Γ (t.openAt Γ.length u) β :=
  HasType.openAt_aux hu ht Γ rfl

theorem HasType.open' {t β α u} (ht : HasType env [α] t β) (hu : HasType env [] u α) :
    HasType env [] (t.open' u) β := by
  simpa [Tm.open'] using ht.openAt (Γ := []) (α := α) hu

/-- A well-typed term mentions only in-scope bound indices. -/
theorem HasType.lc {Γ t α} (h : HasType env Γ t α) : t.LC Γ.length = true := by
  induction h with
  | bvar hi =>
    simp [Tm.LC, (List.getElem?_eq_some_iff.1 hi).1]
  | fvar x α =>
    simp [Tm.LC]
  | const hconst hinst =>
    simp [Tm.LC]
  | app _ _ ihf iha =>
    simp [Tm.LC, ihf, iha]
  | lam _ ih =>
    simpa [Tm.LC, List.length] using ih

theorem HasType.lc0 {t α} (h : HasType env [] t α) : t.LC 0 = true :=
  h.lc

/-- A well-typed term never mentions a constant that is not in the signature. -/
theorem HasType.not_hasConst_of_fresh {Γ t α n}
    (h : HasType env Γ t α) (hn : env.constants n = none) :
    t.hasConst n = false := by
  induction h with
  | bvar hi =>
    rfl
  | fvar x α =>
    rfl
  | const hconst hinst =>
    simp [Tm.hasConst]
    rintro rfl
    simp [hn] at hconst
  | app _ _ ihf iha =>
    simp [Tm.hasConst, ihf, iha]
  | lam _ ih =>
    simpa [Tm.hasConst] using ih

/-- Place a term under one extra binder at de Bruijn index `c`. -/
theorem HasType.shift_at {Γ t α} (h : HasType env Γ t α) (γ : Ty) :
    ∀ c, HasType env (Γ.insertIdx c γ) (t.shift 1 c) α := by
  induction h with
  | bvar hi =>
    rename_i i
    intro c
    by_cases hlt : i < c
    · have hs : (Tm.bvar i).shift 1 c = Tm.bvar i := by simp [Tm.shift, hlt]
      rw [hs]
      exact HasType.bvar ((List.getElem?_insertIdx_of_lt hlt).trans hi)
    · have hle : c ≤ i := Nat.le_of_not_gt hlt
      have hs : (Tm.bvar i).shift 1 c = Tm.bvar (i + 1) := by
        simp [Tm.shift, hlt]
      rw [hs]
      exact HasType.bvar
        ((List.getElem?_insertIdx_of_gt (Nat.lt_succ_of_le hle)).trans hi)
  | fvar x α =>
    intro c
    simp [Tm.shift]
    exact HasType.fvar x α
  | const hconst hinst =>
    intro c
    simp [Tm.shift]
    exact HasType.const hconst hinst
  | app _ _ ihf iha =>
    intro c
    simpa [Tm.shift] using HasType.app (ihf c) (iha c)
  | lam _ ih =>
    intro c
    apply HasType.lam
    simpa [Tm.shift, List.insertIdx_succ_cons] using ih (c + 1)

/-- Place a term under one extra innermost binder. -/
theorem HasType.shift0 {Γ t α} (γ : Ty) (h : HasType env Γ t α) :
    HasType env (γ :: Γ) (t.shift 1 0) α := by
  simpa [List.insertIdx_zero] using h.shift_at γ 0

/-- The equality constant at type `α`. -/
theorem HasType.eqConst [Env.HasEq env] {Γ} (α : Ty) :
    HasType env Γ (Tm.eqConst α) (α ↝ α ↝ .bool) :=
  HasType.const Env.HasEq.eq_const (eqTy_isInstanceOf α)

/-- The Hilbert-choice constant at type `α`. -/
theorem HasType.selectConst [Env.HasSelect env] {Γ} (α : Ty) :
    HasType env Γ (Tm.selectConst α) ((α ↝ .bool) ↝ α) :=
  HasType.const Env.HasSelect.select_const (selectTy_isInstanceOf α)

/-- Equations are booleans when both sides share a type. -/
theorem HasType.mkEq [Env.HasEq env] {Γ s t α}
    (hs : HasType env Γ s α) (ht : HasType env Γ t α) :
    HasType env Γ (Tm.mkEq α s t) .bool :=
  HasType.app (HasType.app (HasType.eqConst α) hs) ht

/-- Inversion for `s = t`. -/
theorem HasType.dest_mkEq {Γ s t α β} (h : HasType env Γ (Tm.mkEq α s t) β) :
    β = .bool ∧ HasType env Γ s α ∧ HasType env Γ t α := by
  cases h with
  | app hf ht =>
    cases hf with
    | app hc hs =>
      cases hc
      exact ⟨rfl, hs, ht⟩

/-- Well-formedness of an environment.

```
Env.WF env  ≔  ∀ p, env.axioms p → HasType env [] p .bool
```

Every postulated axiom must be a **closed boolean sentence in this
signature**.  `HasType env [] p .bool` is three facts at once:

1. **Declared constants only.**  Every `const n inst` in `p` is in
   `env.constants`, at an instance of the stored generic type.
2. **Locally closed.**  No dangling `bvar`s (`p.LC 0`).  A theorem
   cannot mention a bound index that has no binder.
3. **A sentence.**  `p` has type `bool`, not an arbitrary term.

The constant table has no extra obligation: every `Ty` is a valid
generic type (schematic type variables allowed).  There is no δ, so a
definition is just the axiom `⊢ c = t`.  `Env.WF.addDef` preserves WF
when the name is fresh and the RHS has the declared type.

`holCore` is WF (no axioms).  `holLogic` and `holEnv` are proved WF by
the `addDef` chain plus typing of the HOL schemas.

`Provable.ax` admits one axiom given its typing; `Provable.of_axiom`
does the same from `env.WF`. -/
def Env.WF (env : Env) : Prop :=
  ∀ p, env.axioms p → HasType env [] p .bool

theorem Env.WF.typed {p} (hwf : env.WF) (hp : env.axioms p) :
    HasType env [] p .bool :=
  hwf p hp

theorem Env.WF.lc0 {p} (hwf : env.WF) (hp : env.axioms p) :
    p.LC 0 = true :=
  (hwf p hp).lc0

theorem Env.WF.addAxiom {ax : Tm} (hwf : env.WF) (hty : HasType env [] ax .bool) :
    (env.addAxiom ax).WF := by
  intro p hp
  match hp with
  | Or.inl heq =>
    subst heq
    exact hty.weakenEnv (Env.LE.addAxiom env p)
  | Or.inr hax =>
    exact (hwf p hax).weakenEnv (Env.LE.addAxiom env ax)

theorem Env.WF.addConst {n : Name} {ty : Ty} (hwf : env.WF)
    (hfresh : env.constants n = none) :
    (env.addConst n ty).WF := by
  intro p hp
  exact (hwf p hp).weakenEnv (Env.LE.addConst_of_fresh hfresh)

theorem Env.WF.addDef [Env.HasEq env] {n : Name} {ty : Ty} {rhs : Tm}
    (hwf : env.WF) (hfresh : env.constants n = none)
    (hn : n ≠ eqName) (hty : HasType env [] rhs ty) :
    (env.addDef n ty rhs).WF := by
  haveI : Env.HasEq (env.addConst n ty) := Env.HasEq.addConst hn
  have hle : env.LE (env.addConst n ty) := Env.LE.addConst_of_fresh hfresh
  have hconst : HasType (env.addConst n ty) [] (.const n ty) ty :=
    HasType.const (by simp) (Ty.isInstanceOf_self ty)
  have heq : HasType (env.addConst n ty) [] (Tm.mkEq ty (.const n ty) rhs) .bool :=
    HasType.mkEq hconst (hty.weakenEnv hle)
  exact (hwf.addConst hfresh).addAxiom heq

theorem Env.WF.addDef_infer [Env.HasEq env] {n : Name} {ty : Ty} {rhs : Tm}
    (hwf : env.WF) (hfresh : env.constants n = none)
    (hn : n ≠ eqName) (hinfer : rhs.infer env [] = some ty) :
    (env.addDef n ty rhs).WF :=
  Env.WF.addDef hwf hfresh hn (HasType.of_infer hinfer)

theorem Env.WF.addAxiom_infer (hwf : env.WF) (ax : Tm) (hinfer : ax.infer env [] = some .bool) :
    (env.addAxiom ax).WF :=
  hwf.addAxiom (HasType.of_infer hinfer)

end HOLean
