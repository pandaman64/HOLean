/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.SetTheory.ZFC.Basic

/-!
# Set-theoretic raw material

Booleans as `{∅, {∅}}`, graph application, and the successor witness
on `ZFSet.omega` used later for the infinity axiom.
-/

open ZFSet

namespace HOLean

/-- Object-logic false: the empty set. -/
def zfFalse : ZFSet := ∅

/-- Object-logic true: `{∅}`. -/
def zfTrue : ZFSet := {∅}

/-- The two-element set interpreting `bool`. -/
def zfBool : ZFSet := {zfFalse, zfTrue}

theorem zfFalse_ne_zfTrue : zfFalse ≠ zfTrue := by
  intro h
  have : (∅ : ZFSet) ∈ zfTrue := by
    simp [zfTrue]
  rw [← h] at this
  exact notMem_empty _ this

theorem zfFalse_mem_zfBool : zfFalse ∈ zfBool := by
  simp [zfBool]

theorem zfTrue_mem_zfBool : zfTrue ∈ zfBool := by
  simp [zfBool]

theorem mem_zfBool {x : ZFSet} : x ∈ zfBool ↔ x = zfFalse ∨ x = zfTrue := by
  simp [zfBool, zfFalse, zfTrue]

/-- Von Neumann successor `n ↦ n ∪ {n}`. -/
def zfSucc (n : ZFSet) : ZFSet :=
  insert n n

noncomputable instance : Definable₁ zfSucc :=
  Classical.allZFSetDefinable _

theorem zfSucc_mem_omega {n : ZFSet} (h : n ∈ omega) : zfSucc n ∈ omega :=
  omega_succ h

theorem zfSucc_inj {n m : ZFSet} (h : zfSucc n = zfSucc m) : n = m := by
  have hn : n ∈ zfSucc m := h ▸ mem_insert n n
  have hm : m ∈ zfSucc n := h.symm ▸ mem_insert m m
  rw [zfSucc, mem_insert_iff] at hn hm
  match hn, hm with
  | Or.inl hnm, _ => exact hnm
  | _, Or.inl hmn => exact hmn.symm
  | Or.inr hnm, Or.inr hmn => exact (mem_asymm hnm hmn).elim

/-- `succ` misses `∅`, so it is not surjective on `omega`. -/
theorem zfSucc_not_surj_omega :
    ∃ n ∈ omega, ∀ m ∈ omega, zfSucc m ≠ n :=
  ⟨∅, omega_zero, fun m _ h =>
    notMem_empty m (by
      have : m ∈ zfSucc m := mem_insert m m
      rw [h] at this
      exact this)⟩

/-- Graph of successor as a function `ω → ω`. -/
noncomputable def zfSuccFun : ZFSet :=
  map zfSucc omega

theorem zfSuccFun_isFunc : IsFunc omega omega zfSuccFun :=
  (map_isFunc (f := zfSucc) (x := omega) (y := omega)).mpr fun _ => zfSucc_mem_omega

/-- Application of a functional graph.  Well-defined when `IsFunc` holds. -/
noncomputable def zfApp (f x : ZFSet) : ZFSet :=
  Classical.epsilon fun y : ZFSet => pair x y ∈ f

theorem zfApp_spec {x y f a : ZFSet} (hf : IsFunc x y f) (ha : a ∈ x) :
    pair a (zfApp f a) ∈ f ∧ zfApp f a ∈ y := by
  obtain ⟨w, hw, _hunq⟩ := hf.2 a ha
  have hex : ∃ z, pair a z ∈ f := ⟨w, hw⟩
  have happ : pair a (zfApp f a) ∈ f := Classical.epsilon_spec hex
  have hmem : zfApp f a ∈ y := (pair_mem_prod.1 (hf.1 happ)).2
  exact ⟨happ, hmem⟩

theorem zfApp_unique {x y f a b : ZFSet}
    (hf : IsFunc x y f) (ha : a ∈ x) (hb : pair a b ∈ f) :
    zfApp f a = b := by
  obtain ⟨w, hw, hunq⟩ := hf.2 a ha
  have happ := (zfApp_spec hf ha).1
  exact (hunq _ happ).trans (hunq _ hb).symm

end HOLean
