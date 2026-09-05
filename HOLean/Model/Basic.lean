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
  have : ∅ ∈ zfTrue := by
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

/-- Application of a functional graph, as a `ZFSet`.

Mathlib's analogue is `Class.fval` (`′`), which applies a *class* function
and returns a `Class`.  Term denotation is defined by recursion into
`ZFSet`, so we keep the same operator (definite description of the unique
`y` with `⟨x, y⟩ ∈ f`) at the set level. -/
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

noncomputable instance (f : ZFSet) : Definable₁ (fun x => zfApp f x) :=
  Classical.allZFSetDefinable _

/-- A functional graph is exactly the graph of its own application.  This is
object-level η: every element of `funs` *is* a graph. -/
theorem zfIsFunc_eq_map {A B f : ZFSet} (hf : IsFunc A B f) :
    f = map (fun x => zfApp f x) A := by
  apply ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_prod.1 (hf.1 hz)
    exact mem_map.2 ⟨x, hx, pair_inj.2 ⟨rfl, zfApp_unique hf hx hz⟩⟩
  · intro hz
    obtain ⟨x, hx, heq⟩ := mem_map.1 hz
    exact heq ▸ (zfApp_spec hf hx).1

/-- Functional graphs are determined by their values. -/
theorem zfIsFunc_ext {A B f g : ZFSet}
    (hf : IsFunc A B f) (hg : IsFunc A B g)
    (h : ∀ x ∈ A, zfApp f x = zfApp g x) : f = g := by
  rw [zfIsFunc_eq_map hf, zfIsFunc_eq_map hg]
  apply ext
  intro z
  simp [mem_map]
  constructor
  · intro ⟨x, hx, heq⟩
    exact ⟨x, hx, h x hx ▸ heq⟩
  · intro ⟨x, hx, heq⟩
    exact ⟨x, hx, (h x hx).symm ▸ heq⟩

noncomputable instance (b : ZFSet) : Definable₁ (fun _ : ZFSet => b) :=
  Classical.allZFSetDefinable _

/-- Constant graph `A → {b}`. -/
noncomputable def zfConst (A b : ZFSet) : ZFSet :=
  map (fun _ => b) A

noncomputable instance (A : ZFSet) : Definable₁ (fun b => zfConst A b) :=
  Classical.allZFSetDefinable _

theorem zfConst_isFunc {A B b : ZFSet} (hb : b ∈ B) :
    IsFunc A B (zfConst A b) :=
  (map_isFunc (f := fun _ : ZFSet => b) (x := A) (y := B)).mpr fun _ _ => hb

theorem zfConst_mem {A B b : ZFSet} (hb : b ∈ B) :
    zfConst A b ∈ funs A B :=
  mem_funs.2 (zfConst_isFunc hb)

theorem zfConst_app {A b x : ZFSet} (hx : x ∈ A) :
    zfApp (zfConst A b) x = b := by
  have hpair : pair x b ∈ zfConst A b :=
    mem_map.2 ⟨x, hx, rfl⟩
  have hb : b ∈ ({b} : ZFSet) := mem_singleton.2 rfl
  exact zfApp_unique (zfConst_isFunc hb) hx hpair

noncomputable instance : Definable₁ (fun x : ZFSet => x) :=
  Classical.allZFSetDefinable _

/-- Identity graph on `A`. -/
noncomputable def zfId (A : ZFSet) : ZFSet :=
  map (fun x => x) A

theorem zfId_isFunc (A : ZFSet) : IsFunc A A (zfId A) :=
  (map_isFunc (f := fun x : ZFSet => x) (x := A) (y := A)).mpr fun _ hx => hx

theorem zfId_mem (A : ZFSet) : zfId A ∈ funs A A :=
  mem_funs.2 (zfId_isFunc A)

theorem zfId_app {A x : ZFSet} (hx : x ∈ A) : zfApp (zfId A) x = x :=
  zfApp_unique (zfId_isFunc A) hx (mem_map.2 ⟨x, hx, rfl⟩)

/-- First projection `λ x y. x` as an element of `funs A (funs B A)`. -/
noncomputable def zfFst (A B : ZFSet) : ZFSet :=
  map (fun x => zfConst B x) A

theorem zfFst_isFunc (A B : ZFSet) : IsFunc A (funs B A) (zfFst A B) :=
  (map_isFunc (f := fun x => zfConst B x) (x := A) (y := funs B A)).mpr
    fun _ hx => zfConst_mem hx

theorem zfFst_mem (A B : ZFSet) : zfFst A B ∈ funs A (funs B A) :=
  mem_funs.2 (zfFst_isFunc A B)

theorem zfFst_app {A B x y : ZFSet} (hx : x ∈ A) (hy : y ∈ B) :
    zfApp (zfApp (zfFst A B) x) y = x := by
  have hx' : zfApp (zfFst A B) x = zfConst B x :=
    zfApp_unique (zfFst_isFunc A B) hx (mem_map.2 ⟨x, hx, rfl⟩)
  rw [hx']
  exact zfConst_app hy

noncomputable instance (B : ZFSet) : Definable₁ (fun _ : ZFSet => zfId B) :=
  Classical.allZFSetDefinable _

/-- Second projection `λ x y. y` as an element of `funs A (funs B B)`. -/
noncomputable def zfSnd (A B : ZFSet) : ZFSet :=
  map (fun _ => zfId B) A

theorem zfSnd_isFunc (A B : ZFSet) : IsFunc A (funs B B) (zfSnd A B) :=
  (map_isFunc (f := fun _ : ZFSet => zfId B) (x := A) (y := funs B B)).mpr
    fun _ _ => zfId_mem B

theorem zfSnd_mem (A B : ZFSet) : zfSnd A B ∈ funs A (funs B B) :=
  mem_funs.2 (zfSnd_isFunc A B)

theorem zfSnd_app {A B x y : ZFSet} (hx : x ∈ A) (hy : y ∈ B) :
    zfApp (zfApp (zfSnd A B) x) y = y := by
  have hx' : zfApp (zfSnd A B) x = zfId B :=
    zfApp_unique (zfSnd_isFunc A B) hx (mem_map.2 ⟨x, hx, rfl⟩)
  rw [hx']
  exact zfId_app hy

theorem zfSuccFun_app {n : ZFSet} (hn : n ∈ omega) :
    zfApp zfSuccFun n = zfSucc n :=
  zfApp_unique zfSuccFun_isFunc hn (mem_map.2 ⟨n, hn, rfl⟩)

/-- Boolean implication, read off the two-element set. -/
theorem zfBool_imp_iff {p q : ZFSet} (hp : p ∈ zfBool) (_hq : q ∈ zfBool) :
    (p = zfTrue → q = zfTrue) ↔ (p = zfFalse ∨ q = zfTrue) := by
  constructor
  · intro h
    match mem_zfBool.1 hp with
    | Or.inl hpF => exact Or.inl hpF
    | Or.inr hpT => exact Or.inr (h hpT)
  · intro h hpT
    match h with
    | Or.inl hpF =>
      rw [hpF] at hpT
      exact (zfFalse_ne_zfTrue hpT).elim
    | Or.inr hqT =>
      exact hqT

theorem zfBool_eq_false_of_ne_true {x : ZFSet} (hx : x ∈ zfBool) (hne : x ≠ zfTrue) :
    x = zfFalse :=
  (mem_zfBool.1 hx).elim id fun h => (hne h).elim

/-- Conjunction as a boolean identity: `r = (p ∧ q)` yields implication. -/
theorem zfBool_imp_from_and {p q r : ZFSet}
    (hp : p ∈ zfBool) (hr : r ∈ zfBool)
    (hand : r = zfTrue ↔ p = zfTrue ∧ q = zfTrue) :
    (r = p) ↔ (p = zfTrue → q = zfTrue) := by
  constructor
  · intro heq hpT
    exact (hand.1 (heq.trans hpT)).2
  · intro himp
    match mem_zfBool.1 hp with
    | Or.inr hpT =>
      have hqT : q = zfTrue := himp hpT
      have hrT : r = zfTrue := hand.2 ⟨hpT, hqT⟩
      exact hrT.trans hpT.symm
    | Or.inl hpF =>
      have hne : r ≠ zfTrue := fun hrT =>
        have hpT := (hand.1 hrT).1
        zfFalse_ne_zfTrue (hpF ▸ hpT)
      exact (zfBool_eq_false_of_ne_true hr hne).trans hpF.symm

/-- Second-order encoding of existence: `∀ q. (∀ x. P x ⇒ q) ⇒ q`. -/
theorem zfBool_exists_iff {A P : ZFSet} :
    (∀ q ∈ zfBool, (∀ x ∈ A, zfApp P x = zfTrue → q = zfTrue) → q = zfTrue) ↔
      ∃ x ∈ A, zfApp P x = zfTrue := by
  constructor
  · intro h
    by_contra hex
    have hnone : ∀ x ∈ A, zfApp P x ≠ zfTrue :=
      fun x hx hpT => hex ⟨x, hx, hpT⟩
    have : zfFalse = zfTrue :=
      h zfFalse zfFalse_mem_zfBool fun x hx hpT => (hnone x hx hpT).elim
    exact zfFalse_ne_zfTrue this
  · intro ⟨x, hx, hpT⟩ q _hq hall
    exact hall x hx hpT

end HOLean
