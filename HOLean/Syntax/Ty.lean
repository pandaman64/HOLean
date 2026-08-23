/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Simple types

Church-style simple types with schematic (ML-style) type variables.

This is the type language of the HOL Light kernel: type variables together with
the primitive constructors `bool`, `ind`, and `fun` (`↝`).  Polymorphism is
*schematic* rather than System F — type variables are implicitly universally
quantified at the level of theorems and instantiated by `INST_TYPE`.
-/

namespace HOLean

/-- Names of schematic type variables and of free term variables. -/
abbrev Name := String

/-- Simple types of HOL. -/
inductive Ty where
  /-- A schematic type variable, e.g. `α`. -/
  | var : Name → Ty
  /-- The type of propositions / booleans. -/
  | bool : Ty
  /-- An infinite type of individuals (used by the infinity axiom). -/
  | ind : Ty
  /-- Function type `α ↝ β`. -/
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr, Inhabited

@[inherit_doc Ty.arrow]
-- Bind tighter than `=` (50) so `t = α ↝ β` means `t = (α ↝ β)`.
scoped infixr:51 " ↝ " => Ty.arrow

/-- A type substitution: the first matching pair wins. Non-variable leftovers
are ignored, matching HOL Light's `type_subst`. -/
abbrev TySubst := List (Name × Ty)

namespace TySubst

def lookup (θ : TySubst) (x : Name) : Option Ty :=
  match θ with
  | [] => none
  | (y, α) :: rest => if y = x then some α else lookup rest x

@[simp] theorem lookup_nil (x : Name) : lookup [] x = none := rfl

@[simp] theorem lookup_cons_self (x : Name) (α : Ty) (rest : TySubst) :
    lookup ((x, α) :: rest) x = some α := by
  simp [lookup]

theorem lookup_cons_of_ne {x y : Name} (α : Ty) (rest : TySubst) (h : y ≠ x) :
    lookup ((y, α) :: rest) x = lookup rest x := by
  simp [lookup, h]

end TySubst

namespace Ty

/-- Instantiate schematic type variables. -/
def inst (θ : TySubst) : Ty → Ty
  | var x => (θ.lookup x).getD (var x)
  | bool => bool
  | ind => ind
  | arrow α β => arrow (α.inst θ) (β.inst θ)

@[simp] theorem inst_bool (θ : TySubst) : bool.inst θ = bool := rfl
@[simp] theorem inst_ind (θ : TySubst) : ind.inst θ = ind := rfl
@[simp] theorem inst_arrow (θ : TySubst) (α β : Ty) :
    (α ↝ β).inst θ = (α.inst θ ↝ β.inst θ) := rfl

@[simp] theorem inst_nil : ∀ α : Ty, inst [] α = α
  | var _ => rfl
  | bool => rfl
  | ind => rfl
  | arrow α β => by simp [inst, inst_nil α, inst_nil β]

/-- Free schematic type variables, left-to-right, without duplicates. -/
def tyvars : Ty → List Name
  | var x => [x]
  | bool => []
  | ind => []
  | arrow α β => α.tyvars ++ β.tyvars.filter (· ∉ α.tyvars)

end Ty

/-- De Bruijn lookup into a bound-variable context (index `0` is the innermost
binder). -/
def Ctx.get : List Ty → Nat → Option Ty
  | [], _ => none
  | α :: _, 0 => some α
  | _ :: Γ, n + 1 => Ctx.get Γ n

@[simp] theorem Ctx.get_nil (i : Nat) : Ctx.get [] i = none := rfl

@[simp] theorem Ctx.get_cons_zero (α : Ty) (Γ : List Ty) :
    Ctx.get (α :: Γ) 0 = some α := rfl

@[simp] theorem Ctx.get_cons_succ (α : Ty) (Γ : List Ty) (n : Nat) :
    Ctx.get (α :: Γ) (n + 1) = Ctx.get Γ n := rfl

theorem Ctx.get_map (f : Ty → Ty) :
    ∀ (Γ : List Ty) (i : Nat), Ctx.get (Γ.map f) i = (Ctx.get Γ i).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: Γ, n + 1 => Ctx.get_map f Γ n

theorem Ctx.get_append_prefix :
    ∀ {Δ Γ : List Ty} {i : Nat},
      i < Δ.length → Ctx.get (Δ ++ Γ) i = Ctx.get Δ i
  | [], Γ, i, h => by cases h
  | β :: Δ, Γ, 0, _ => by simp [Ctx.get]
  | β :: Δ, Γ, n + 1, h => by
    have : n < Δ.length := Nat.lt_of_succ_lt_succ h
    simpa [Ctx.get] using Ctx.get_append_prefix (Δ := Δ) (Γ := Γ) this

theorem Ctx.get_append_left {α : Ty} :
    ∀ {Γ Δ : List Ty} {i : Nat}, Ctx.get Γ i = some α → Ctx.get (Γ ++ Δ) i = some α
  | [], _, _, h => by cases h
  | _ :: _, _, 0, h => by
    simp at h
    simp [h]
  | _ :: Γ, Δ, n + 1, h => by
    simp at h
    simpa using Ctx.get_append_left (Γ := Γ) (Δ := Δ) (i := n) h

theorem Ctx.get_eq_some_unique {Γ : List Ty} {i : Nat} {α β : Ty}
    (hα : Ctx.get Γ i = some α) (hβ : Ctx.get Γ i = some β) : α = β := by
  rw [hα] at hβ
  injection hβ

/-- Insert `γ` so that it becomes de Bruijn index `c` (outer binders stay
at indices `> c`). -/
def insertTy : Nat → Ty → List Ty → List Ty
  | 0, γ, Γ => γ :: Γ
  | _n + 1, γ, [] => [γ]
  | n + 1, γ, β :: Γ => β :: insertTy n γ Γ

theorem Ctx.get_insertTy_lt {γ α : Ty} :
    ∀ {c i : Nat} {Γ : List Ty},
      Ctx.get Γ i = some α → i < c → Ctx.get (insertTy c γ Γ) i = some α
  | 0, i, Γ, hi, hlt => by cases hlt
  | n + 1, i, [], hi, _ => by cases hi
  | n + 1, i, β :: Γ, hi, hlt => by
    cases i with
    | zero =>
      simpa [insertTy, Ctx.get] using hi
    | succ i =>
      have : i < n := Nat.lt_of_succ_lt_succ hlt
      simp [Ctx.get] at hi
      simpa [insertTy, Ctx.get] using
        Ctx.get_insertTy_lt (γ := γ) (α := α) (c := n) (i := i) (Γ := Γ) hi this

theorem Ctx.get_insertTy_ge {γ α : Ty} :
    ∀ {c i : Nat} {Γ : List Ty},
      Ctx.get Γ i = some α → c ≤ i → Ctx.get (insertTy c γ Γ) (i + 1) = some α
  | 0, i, Γ, hi, _ => by
    simpa [insertTy, Ctx.get] using hi
  | n + 1, i, [], hi, _ => by cases hi
  | n + 1, i, β :: Γ, hi, hle => by
    cases i with
    | zero =>
      exact (Nat.not_succ_le_zero n hle).elim
    | succ i =>
      have : n ≤ i := Nat.le_of_succ_le_succ hle
      simp [Ctx.get] at hi
      simpa [insertTy, Ctx.get] using
        Ctx.get_insertTy_ge (γ := γ) (α := α) (c := n) (i := i) (Γ := Γ) hi this

/-- Lookup in a snoc-context: the last index is the extra binder. -/
theorem Ctx.get_snoc (Δ : List Ty) (α : Ty) (i : Nat) :
    Ctx.get (Δ ++ [α]) i = if i = Δ.length then some α else Ctx.get Δ i := by
  induction Δ generalizing i with
  | nil =>
    cases i <;> simp [Ctx.get]
  | cons γ Δ ih =>
    cases i with
    | zero =>
      simp [List.length]
    | succ n =>
      simp [ih n]

end HOLean
