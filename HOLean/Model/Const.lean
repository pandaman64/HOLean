/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Model.Ty
import HOLean.Syntax.Const

/-!
# Primitive constant graphs

Equality is the characteristic function of extensional equality.
Hilbert choice picks a witness of a predicate graph, or an arbitrary
element of a nonempty type.
-/

open ZFSet Classical

namespace HOLean

/-- Boolean of a meta-level equality test. -/
noncomputable def zfBoolOfEq (x y : ZFSet) : ZFSet :=
  if x = y then zfTrue else zfFalse

noncomputable instance (x : ZFSet) : Definable₁ (zfBoolOfEq x) :=
  Classical.allZFSetDefinable _

theorem zfBoolOfEq_mem (x y : ZFSet) : zfBoolOfEq x y ∈ zfBool := by
  by_cases hxy : x = y
  · simp [zfBoolOfEq, hxy, zfTrue_mem_zfBool]
  · simp [zfBoolOfEq, hxy, zfFalse_mem_zfBool]

@[simp] theorem zfBoolOfEq_self (x : ZFSet) : zfBoolOfEq x x = zfTrue := by
  simp [zfBoolOfEq]

theorem zfBoolOfEq_true_iff (x y : ZFSet) :
    zfBoolOfEq x y = zfTrue ↔ x = y := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact hxy
    · simp [zfBoolOfEq, hxy] at h
      exact (zfFalse_ne_zfTrue h).elim
  · intro h
    simp [zfBoolOfEq, h]

theorem map_congr {f g : ZFSet → ZFSet} [Definable₁ f] [Definable₁ g]
    {A : ZFSet} (h : ∀ x ∈ A, f x = g x) : map f A = map g A := by
  apply ext
  intro z
  simp [mem_map]
  constructor
  · intro ⟨x, hx, heq⟩
    exact ⟨x, hx, h x hx ▸ heq⟩
  · intro ⟨x, hx, heq⟩
    exact ⟨x, hx, (h x hx).symm ▸ heq⟩

/-- Characteristic function of `x = ·` on a set `A`, landing in `zfBool`. -/
noncomputable def zfEqAt (A x : ZFSet) : ZFSet :=
  map (zfBoolOfEq x) A

noncomputable instance (A : ZFSet) : Definable₁ (zfEqAt A) :=
  Classical.allZFSetDefinable _

theorem zfEqAt_isFunc (A x : ZFSet) : IsFunc A zfBool (zfEqAt A x) :=
  (map_isFunc (f := zfBoolOfEq x) (x := A) (y := zfBool)).mpr
    fun _ _ => zfBoolOfEq_mem _ _

theorem zfEqAt_mem (A x : ZFSet) : zfEqAt A x ∈ funs A zfBool :=
  mem_funs.2 (zfEqAt_isFunc A x)

theorem zfEqAt_app {A x y : ZFSet} (hy : y ∈ A) :
    zfApp (zfEqAt A x) y = zfBoolOfEq x y := by
  have hpair : pair y (zfBoolOfEq x y) ∈ zfEqAt A x :=
    mem_map.2 ⟨y, hy, rfl⟩
  exact zfApp_unique (zfEqAt_isFunc A x) hy hpair

/-- Curried equality graph: an element of `funs A (funs A zfBool)`. -/
noncomputable def zfEq (A : ZFSet) : ZFSet :=
  map (zfEqAt A) A

theorem zfEq_isFunc (A : ZFSet) : IsFunc A (funs A zfBool) (zfEq A) :=
  (map_isFunc (f := zfEqAt A) (x := A) (y := funs A zfBool)).mpr
    fun _ _ => zfEqAt_mem A _

theorem zfEq_mem (A : ZFSet) : zfEq A ∈ funs A (funs A zfBool) :=
  mem_funs.2 (zfEq_isFunc A)

theorem zfEq_app {A x : ZFSet} (hx : x ∈ A) : zfApp (zfEq A) x = zfEqAt A x := by
  have hpair : pair x (zfEqAt A x) ∈ zfEq A := mem_map.2 ⟨x, hx, rfl⟩
  exact zfApp_unique (zfEq_isFunc A) hx hpair

theorem zfEq_app₂ {A x y : ZFSet} (hx : x ∈ A) (hy : y ∈ A) :
    zfApp (zfApp (zfEq A) x) y = zfBoolOfEq x y := by
  rw [zfEq_app hx, zfEqAt_app hy]

/-- A valuation that sends every type variable to a nonempty set. -/
def TyVal.Nonempty (ρ : TyVal) : Prop :=
  ∀ x, (ρ x).Nonempty

/-- Standard-model types are nonempty when type variables are. -/
theorem Ty.denote_nonempty {ρ : TyVal} (hρ : ρ.Nonempty) :
    ∀ α : Ty, (α.denote ρ).Nonempty
  | .var x => hρ x
  | .bool => ⟨zfTrue, zfTrue_mem_zfBool⟩
  | .ind => ⟨∅, omega_zero⟩
  | .arrow α β => by
    obtain ⟨b, hb⟩ := Ty.denote_nonempty hρ β
    exact ⟨zfConst (α.denote ρ) b, zfConst_mem hb⟩

/-- Choice on a predicate graph: a witness of `P` if any, else an
arbitrary element of the nonempty set `A`. -/
noncomputable def zfChoose (A : ZFSet) (hA : A.Nonempty) (P : ZFSet) : ZFSet :=
  let s := A.sep (fun x => zfApp P x = zfTrue)
  if h : s.Nonempty then Classical.choose h else Classical.choose hA

theorem zfChoose_mem (A : ZFSet) (hA : A.Nonempty) (P : ZFSet) :
    zfChoose A hA P ∈ A := by
  unfold zfChoose
  dsimp
  split
  · next h =>
    exact (mem_sep.1 (Classical.choose_spec h)).1
  · exact Classical.choose_spec hA

/-- If `P` holds of some element of `A`, choice returns a witness. -/
theorem zfChoose_spec {A P : ZFSet} (hA : A.Nonempty)
    (hP : ∃ x ∈ A, zfApp P x = zfTrue) :
    zfApp P (zfChoose A hA P) = zfTrue := by
  obtain ⟨x, hx, hPx⟩ := hP
  have hs : (A.sep (fun y => zfApp P y = zfTrue)).Nonempty :=
    ⟨x, mem_sep.2 ⟨hx, hPx⟩⟩
  unfold zfChoose
  dsimp
  rw [dif_pos hs]
  have hch := mem_sep.1 (Classical.choose_spec hs)
  exact hch.2

noncomputable instance (A : ZFSet) (hA : A.Nonempty) :
    Definable₁ (zfChoose A hA) :=
  Classical.allZFSetDefinable _

/-- Hilbert ε as a graph `(A ↝ bool) ↝ A`. -/
noncomputable def zfSelect (A : ZFSet) (hA : A.Nonempty) : ZFSet :=
  map (zfChoose A hA) (funs A zfBool)

theorem zfSelect_isFunc (A : ZFSet) (hA : A.Nonempty) :
    IsFunc (funs A zfBool) A (zfSelect A hA) :=
  (map_isFunc (f := zfChoose A hA)
    (x := funs A zfBool) (y := A)).mpr fun _ _ => zfChoose_mem A hA _

theorem zfSelect_mem (A : ZFSet) (hA : A.Nonempty) :
    zfSelect A hA ∈ funs (funs A zfBool) A :=
  mem_funs.2 (zfSelect_isFunc A hA)

theorem zfSelect_app {A P : ZFSet} (hA : A.Nonempty) (hP : P ∈ funs A zfBool) :
    zfApp (zfSelect A hA) P = zfChoose A hA P := by
  have hpair : pair P (zfChoose A hA P) ∈ zfSelect A hA :=
    mem_map.2 ⟨P, hP, rfl⟩
  exact zfApp_unique (zfSelect_isFunc A hA) hP hpair

theorem eqTy_instantiates_iff {inst : Ty} :
    eqTy.instantiates inst ↔ ∃ α, inst = α ↝ α ↝ .bool := by
  constructor
  · intro ⟨θ, h⟩
    refine ⟨(θ.lookup primTyVar).getD (.var primTyVar), ?_⟩
    simpa [eqTy, Ty.inst] using h.symm
  · intro ⟨α, h⟩
    exact h ▸ eqTy_instantiates α

theorem selectTy_instantiates_iff {inst : Ty} :
    selectTy.instantiates inst ↔ ∃ α, inst = (α ↝ .bool) ↝ α := by
  constructor
  · intro ⟨θ, h⟩
    refine ⟨(θ.lookup primTyVar).getD (.var primTyVar), ?_⟩
    simpa [selectTy, Ty.inst] using h.symm
  · intro ⟨α, h⟩
    exact h ▸ selectTy_instantiates α

end HOLean
