/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Model.Tm
import HOLean.Kernel

/-!
# Denotation commutes with the kernel operations

These lemmas are the semantic counterparts of the operations the ten
rules actually perform.  `Provable.sound` and `EnvModel.addDef` are the
clients; nothing here is an inference rule.

* `denote_mkEq_true_iff` — REFL, TRANS, MK_COMB, EQ_MP, DEDUCT_ANTISYM, ABS
* `denote_fresh` / `denote_close` — ABS (`x ∉ FV(Γ)`, then close the fvar)
* `denote_beta` / `denote_open'` — BETA
* `denote_instTy` — INST_TYPE
* `denote_applySubst` — INST
* `denote_reindex` / `denote_interp_eq` — transport `ax_ok` along `TyVal.inst`
* `denote_no_fvars` / `denote_interp_except` — `addDef` (closed RHS, fresh name)
* `denote_shift1` — push a closed-at-cutoff term under one extra binder (η, expansions)
-/

open ZFSet Classical

namespace HOLean

variable {env : Env} {ρ : TyVal}

theorem Tm.denote_eqConst [Env.HasEq env] (I : EnvInterp env ρ)
    (heq : ∀ α, I.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ))
    (ξ : FVarVal ρ) (vs : List ZFSet) (α : Ty) :
    (Tm.eqConst α).denote I ξ vs = zfEq (α.denote ρ) :=
  heq α

theorem Tm.denote_mkEq [Env.HasEq env] (I : EnvInterp env ρ)
    (heq : ∀ α, I.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ))
    (ξ : FVarVal ρ) {Γ s t α} (hs : HasType env Γ s α) (ht : HasType env Γ t α)
    (vs : CtxVal ρ Γ) :
    (Tm.mkEq α s t).denote I ξ vs.vals =
      zfBoolOfEq (s.denote I ξ vs.vals) (t.denote I ξ vs.vals) := by
  have hsM := hs.denote_mem I ξ vs
  have htM := ht.denote_mem I ξ vs
  simp [HasType.denote] at hsM htM
  simp [Tm.mkEq, Tm.denote, Tm.eqConst, heq]
  exact zfEq_app₂ hsM htM

theorem Tm.denote_mkEq_true_iff [Env.HasEq env] (I : EnvInterp env ρ)
    (heq : ∀ α, I.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ))
    (ξ : FVarVal ρ) {Γ s t α} (hs : HasType env Γ s α) (ht : HasType env Γ t α)
    (vs : CtxVal ρ Γ) :
    (Tm.mkEq α s t).denote I ξ vs.vals = zfTrue ↔
      s.denote I ξ vs.vals = t.denote I ξ vs.vals := by
  rw [Tm.denote_mkEq I heq ξ hs ht vs, zfBoolOfEq_true_iff]

theorem Tm.denote_mkEq_true_iff_nil [Env.HasEq env] (I : EnvInterp env ρ)
    (heq : ∀ α, I.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ))
    (ξ : FVarVal ρ) {s t α} (hs : HasType env [] s α) (ht : HasType env [] t α) :
    (Tm.mkEq α s t).denote I ξ [] = zfTrue ↔
      s.denote I ξ [] = t.denote I ξ [] := by
  simpa [CtxVal.nil] using Tm.denote_mkEq_true_iff I heq ξ hs ht (CtxVal.nil ρ)

/-- A locally closed term does not read bound values past its cutoff. -/
theorem Tm.denote_LC_drop (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs extra : List ZFSet) (h : t.LC vs.length = true) :
    t.denote I ξ (vs ++ extra) = t.denote I ξ vs := by
  induction t generalizing vs with
  | bvar i =>
    simp [Tm.LC] at h
    simp [Tm.denote, List.getElem?_append_left h]
  | fvar y β =>
    rfl
  | const n β =>
    rfl
  | app f a ihf iha =>
    simp [Tm.LC] at h
    simp [Tm.denote, ihf vs h.1, iha vs h.2]
  | lam β t ih =>
    simp [Tm.LC] at h
    simp [Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    simpa [List.length] using ih (x :: vs) h

theorem Tm.denote_LC0 (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : List ZFSet) (h : t.LC 0 = true) :
    t.denote I ξ vs = t.denote I ξ [] :=
  Tm.denote_LC_drop t I ξ [] vs h

theorem List.getElem?_insert_dummy (pre post : List ZFSet) (dummy : ZFSet)
    (i : Nat) :
    (pre ++ dummy :: post)[if i < pre.length then i else i + 1]? =
      (pre ++ post)[i]? := by
  by_cases hlt : i < pre.length
  · simp [hlt, List.getElem?_append_left hlt]
  · have hge : pre.length ≤ i := Nat.le_of_not_gt hlt
    have hi1 : pre.length ≤ i + 1 := Nat.le_succ_of_le hge
    have hsucc : i + 1 - pre.length = i - pre.length + 1 := by omega
    simp [hlt, List.getElem?_append_right (l₁ := pre) hi1,
      List.getElem?_append_right (l₁ := pre) hge, hsucc]

/-- Inserting a dummy at cutoff `pre.length` does not change denotation. -/
theorem Tm.denote_shift1 (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (pre : List ZFSet) (dummy : ZFSet) (post : List ZFSet) :
    (t.shift 1 pre.length).denote I ξ (pre ++ dummy :: post) =
      t.denote I ξ (pre ++ post) := by
  induction t generalizing pre with
  | bvar i =>
    simp [Tm.shift, Tm.denote]
    by_cases hlt : i < pre.length
    · simp [hlt, List.getElem?_append_left hlt]
    · simp [hlt]
      have := List.getElem?_insert_dummy pre post dummy i
      simp [hlt] at this
      exact congrArg (fun o => o.getD ∅) this
  | fvar y β =>
    rfl
  | const n β =>
    rfl
  | app f a ihf iha =>
    simp [Tm.shift, Tm.denote, ihf pre, iha pre]
  | lam β t ih =>
    simp [Tm.shift, Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    simpa [List.length, List.cons_append] using ih (x :: pre)

theorem Tm.denote_shift1_cons (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (dummy : ZFSet) (vs : List ZFSet) :
    (t.shift 1 0).denote I ξ (dummy :: vs) = t.denote I ξ vs :=
  Tm.denote_shift1 t I ξ [] dummy vs

/-- Denotation ignores a free variable that does not occur. -/
theorem Tm.denote_fresh (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : List ZFSet) {x α v} (hv : v ∈ α.denote ρ)
    (hf : t.freeIn x α = false) :
    t.denote I (ξ.update x α v hv) vs = t.denote I ξ vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar y β =>
    have hne : ¬ (y = x ∧ β = α) := by
      simp [Tm.freeIn] at hf
      exact fun ⟨hy, hβ⟩ => hf hy hβ
    simp [Tm.denote, FVarVal.update, hne]
  | const n β =>
    rfl
  | app f a ihf iha =>
    simp [Tm.freeIn] at hf
    simp [Tm.denote, ihf vs hf.1, iha vs hf.2]
  | lam β t ih =>
    simp [Tm.freeIn] at hf
    simp [Tm.denote]
    apply map_congr
    intro z hz
    simp [lamFn, hz]
    exact ih (z :: vs) hf

/-- Closing at cutoff `k = vs.length` on a term that is LC at that cutoff. -/
theorem Tm.denote_closeAt (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : List ZFSet) {x α v} (hv : v ∈ α.denote ρ)
    (hLC : t.LC vs.length = true) :
    (t.closeAt vs.length x α).denote I ξ (vs ++ [v]) =
      t.denote I (ξ.update x α v hv) vs := by
  induction t generalizing vs with
  | bvar i =>
    simp [Tm.LC] at hLC
    simp [Tm.closeAt, Tm.denote, List.getElem?_append_left hLC]
  | fvar y β =>
    by_cases h : y = x ∧ β = α
    · simp [Tm.closeAt, Tm.denote, h, FVarVal.update]
    · simp [Tm.closeAt, Tm.denote, h, FVarVal.update]
  | const n β =>
    rfl
  | app f a ihf iha =>
    simp [Tm.LC] at hLC
    simp [Tm.closeAt, Tm.denote, ihf vs hLC.1, iha vs hLC.2]
  | lam β t ih =>
    simp [Tm.LC] at hLC
    simp [Tm.closeAt, Tm.denote]
    apply map_congr
    intro z hz
    simp [lamFn, hz]
    simpa [List.length] using ih (z :: vs) hLC

theorem Tm.denote_close (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    {x α v} (hv : v ∈ α.denote ρ) (hLC : t.LC 0 = true) :
    (t.close x α).denote I ξ [v] = t.denote I (ξ.update x α v hv) [] :=
  Tm.denote_closeAt t I ξ [] hv hLC

/-- Opening index `k = vs.length` as a closed term. -/
theorem Tm.denote_openAt (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    {α : Ty} {u : Tm} (hu : HasType env [] u α)
    (vs : List ZFSet) :
    (t.openAt vs.length u).denote I ξ vs =
      t.denote I ξ (vs ++ [u.denote I ξ []]) := by
  induction t generalizing vs with
  | bvar i =>
    simp [Tm.openAt, Tm.denote]
    by_cases hi : i = vs.length
    · subst hi
      simp [Tm.denote_LC0 u I ξ vs hu.lc0]
    · simp [hi, Tm.denote]
      by_cases hlt : i < vs.length
      · simp [List.getElem?_append_left hlt]
      · have hge : vs.length ≤ i := Nat.le_of_not_gt hlt
        have hnone : vs[i]? = none := List.getElem?_eq_none hge
        have hnone' : (vs ++ [u.denote I ξ []])[i]? = none := by
          apply List.getElem?_eq_none
          simp
          omega
        simp [hnone, hnone']
  | fvar y β =>
    rfl
  | const n β =>
    rfl
  | app f a ihf iha =>
    simp [Tm.openAt, Tm.denote, ihf vs, iha vs]
  | lam β t ih =>
    simp [Tm.openAt, Tm.denote]
    apply map_congr
    intro z hz
    simp [lamFn, hz]
    simpa [List.length] using ih (z :: vs)

theorem Tm.denote_open' (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    {α : Ty} {u : Tm} (hu : HasType env [] u α) :
    (t.open' u).denote I ξ [] = t.denote I ξ [u.denote I ξ []] :=
  Tm.denote_openAt t I ξ hu []

/-- Applying the graph of a λ is opening the body.  Stated on raw
`Tm.denote` so we never unfold `map` (whose `Definable₁` instance is
not definitionally unique). -/
theorem Tm.denote_beta {α β : Ty} {t u : Tm}
    (ht : HasType env [α] t β) (hu : HasType env [] u α)
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) :
    (Tm.app (.lam α t) u).denote I ξ [] =
      (t.open' u).denote I ξ [] := by
  have hmem := hu.denote_mem I ξ (CtxVal.nil ρ)
  have happ := HasType.denote_lam_app ht I ξ (CtxVal.nil ρ) hmem
  simp only [HasType.denote, CtxVal.nil, CtxVal.cons] at happ
  change zfApp ((Tm.lam α t).denote I ξ []) (u.denote I ξ []) =
    (t.open' u).denote I ξ []
  rw [happ, Tm.denote_open' t I ξ hu]

/-- Type instantiation commutes with denotation on raw terms. -/
theorem Tm.denote_instTy (t : Tm) (θ : TySubst)
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (t.instTy θ).denote I ξ vs = t.denote (I.inst θ) (ξ.pull θ) vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar x α =>
    rfl
  | const n α =>
    rfl
  | app f a ihf iha =>
    simp [Tm.instTy, Tm.denote, ihf, iha]
  | lam α t ih =>
    apply ext
    intro z
    have hdom : (α.inst θ).denote ρ = α.denote (ρ.inst θ) := Ty.denote_inst ρ θ α
    simp [Tm.instTy, Tm.denote, mem_map]
    constructor
    · intro ⟨x, hx, heq⟩
      refine ⟨x, hdom ▸ hx, ?_⟩
      have hx' : x ∈ α.denote (ρ.inst θ) := hdom ▸ hx
      simp [lamFn, hx, hx'] at heq ⊢
      exact (ih (x :: vs)).symm ▸ heq
    · intro ⟨x, hx, heq⟩
      refine ⟨x, hdom.symm ▸ hx, ?_⟩
      have hx' : x ∈ (α.inst θ).denote ρ := hdom.symm ▸ hx
      simp [lamFn, hx, hx'] at heq ⊢
      exact ih (x :: vs) ▸ heq

/-- Simultaneous substitution of closed replacements. -/
noncomputable def FVarVal.apply (ξ : FVarVal ρ) (I : EnvInterp env ρ)
    (σ : Tm.Subst) (hσ : σ.Ok env) : FVarVal ρ where
  val x α :=
    match h : σ.lookup x α with
    | some u => u.denote I ξ []
    | none => ξ.val x α
  mem x α := by
    cases h : σ.lookup x α with
    | some u =>
      have := (hσ x α u h).denote_mem I ξ (CtxVal.nil ρ)
      simpa [HasType.denote, CtxVal.nil] using this
    | none =>
      exact ξ.mem x α

theorem HasType.denote_applySubst {Γ t β σ} (ht : HasType env Γ t β)
    (hσ : σ.Ok env) (I : EnvInterp env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (t.applySubst σ).denote I ξ vs.vals =
      t.denote I (ξ.apply I σ hσ) vs.vals := by
  induction ht with
  | bvar hi =>
    rfl
  | fvar x α =>
    simp [Tm.applySubst, Tm.denote, FVarVal.apply]
    cases hlook : σ.lookup x α with
    | none =>
      rfl
    | some u =>
      exact Tm.denote_LC0 u I ξ vs.vals (hσ x α u hlook).lc0
  | const hconst hinst =>
    rfl
  | app hf ha ihf iha =>
    simp [Tm.applySubst, Tm.denote, ihf vs, iha vs]
  | lam ht ih =>
    simp [Tm.applySubst, Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    simpa [CtxVal.cons] using ih (vs.cons x hx)

/-- Denotation depends only on the interpretation table, not the `mem` proof. -/
theorem Tm.denote_interp_eq (t : Tm) (I I' : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : List ZFSet) (h : ∀ n α, I.interp n α = I'.interp n α) :
    t.denote I ξ vs = t.denote I' ξ vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar x α =>
    rfl
  | const n α =>
    exact h n α
  | app f a ihf iha =>
    simp [Tm.denote, ihf vs, iha vs]
  | lam α t ih =>
    simp [Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    exact ih (x :: vs)

/-- Denotation is unchanged when type universes are pointwise equal. -/
theorem Tm.denote_reindex (t : Tm) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    {ρ' : TyVal} (h : ∀ α : Ty, Ty.denote ρ α = Ty.denote ρ' α) (vs : List ZFSet) :
    t.denote I ξ vs = t.denote (I.reindex h) (ξ.congr h) vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar x α =>
    rfl
  | const n α =>
    rfl
  | app f a ihf iha =>
    simp [Tm.denote, ihf, iha]
  | lam α t ih =>
    apply ext
    intro z
    have hdom := h α
    simp [Tm.denote, mem_map]
    constructor
    · intro ⟨x, hx, heq⟩
      refine ⟨x, hdom ▸ hx, ?_⟩
      have hx' : x ∈ α.denote ρ' := hdom ▸ hx
      simp [lamFn, hx, hx'] at heq ⊢
      exact ih (x :: vs) ▸ heq
    · intro ⟨x, hx, heq⟩
      refine ⟨x, hdom.symm ▸ hx, ?_⟩
      have hx' : x ∈ α.denote ρ := hdom.symm ▸ hx
      simp [lamFn, hx, hx'] at heq ⊢
      exact (ih (x :: vs)).symm ▸ heq

/-- Two free-variable assignments that agree on the fvars of `t` give the
same denotation. -/
theorem Tm.denote_fvarVal (t : Tm) (I : EnvInterp env ρ) (ξ ξ' : FVarVal ρ)
    (vs : List ZFSet)
    (h : ∀ x α, t.freeIn x α = false ∨ ξ.val x α = ξ'.val x α) :
    t.denote I ξ vs = t.denote I ξ' vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar y β =>
    cases h y β with
    | inl hf =>
      simp [Tm.freeIn] at hf
    | inr heq =>
      simpa [Tm.denote] using heq
  | const n α =>
    rfl
  | app f a ihf iha =>
    simp [Tm.denote, ihf vs (fun x α =>
      match h x α with
      | Or.inl hf =>
        Or.inl (by simp [Tm.freeIn, Bool.or_eq_false_iff] at hf; exact hf.1)
      | Or.inr heq =>
        Or.inr heq),
      iha vs (fun x α =>
        match h x α with
        | Or.inl hf =>
          Or.inl (by simp [Tm.freeIn, Bool.or_eq_false_iff] at hf; exact hf.2)
        | Or.inr heq =>
          Or.inr heq)]
  | lam α t ih =>
    simp [Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    exact ih (x :: vs) h

theorem Tm.denote_no_fvars (t : Tm) (I : EnvInterp env ρ) (ξ ξ' : FVarVal ρ)
    (vs : List ZFSet) (h : ∀ x α, t.freeIn x α = false) :
    t.denote I ξ vs = t.denote I ξ' vs :=
  Tm.denote_fvarVal t I ξ ξ' vs fun x α => Or.inl (h x α)

/-- Denotation ignores the environment name: only the interp table matters. -/
theorem Tm.denote_interp_eq_env {env' : Env} (t : Tm)
    (I : EnvInterp env ρ) (I' : EnvInterp env' ρ) (ξ : FVarVal ρ)
    (vs : List ZFSet) (h : ∀ n α, I.interp n α = I'.interp n α) :
    t.denote I ξ vs = t.denote I' ξ vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar x α =>
    rfl
  | const n α =>
    exact h n α
  | app f a ihf iha =>
    simp [Tm.denote, ihf vs, iha vs]
  | lam α t ih =>
    simp [Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    exact ih (x :: vs)

/-- Tables that agree off a missing constant give the same denotation. -/
theorem Tm.denote_interp_except {env' : Env} {n : Name} (t : Tm)
    (I : EnvInterp env ρ) (I' : EnvInterp env' ρ) (ξ : FVarVal ρ)
    (vs : List ZFSet) (hne : t.hasConst n = false)
    (h : ∀ m α, m ≠ n → I.interp m α = I'.interp m α) :
    t.denote I ξ vs = t.denote I' ξ vs := by
  induction t generalizing vs with
  | bvar i =>
    rfl
  | fvar x α =>
    rfl
  | const c α =>
    simp [Tm.hasConst] at hne
    exact h c α hne
  | app f a ihf iha =>
    simp [Tm.hasConst, Bool.or_eq_false_iff] at hne
    simp [Tm.denote, ihf vs hne.1, iha vs hne.2]
  | lam α t ih =>
    simp [Tm.hasConst] at hne
    simp [Tm.denote]
    apply map_congr
    intro x hx
    simp [lamFn, hx]
    exact ih (x :: vs) hne

end HOLean
