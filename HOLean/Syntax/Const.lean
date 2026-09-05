/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Ty

/-!
# Primitive constants

The HOL Light kernel starts with equality; Hilbert choice is the second
primitive.  Every other logical constant is a definitional extension of an
environment (`Env.addDef`).

Constants are identified by `Name`.  The initial signature assigns each
primitive a *generic* type (type variables allowed).  A term
`Tm.const n inst` carries the *instantiated* type `inst`, which must be a
substitution instance of the generic type (`Ty.instantiates`).
-/

namespace HOLean

/-- Name of object-logic equality. -/
def eqName : Name := "eq"

/-- Name of Hilbert ε / `@`. -/
def selectName : Name := "select"

/-- Schematic type parameters of the primitive and defined constants. -/
def primTyVar : Name := "A"

/-- Second schematic parameter, used by `ONE_ONE` / `ONTO`. -/
def primTyVarB : Name := "B"

/-- Generic type of equality: `A ↝ A ↝ bool`. -/
def eqTy : Ty :=
  .var primTyVar ↝ .var primTyVar ↝ .bool

/-- Generic type of Hilbert choice: `(A ↝ bool) ↝ A`. -/
def selectTy : Ty :=
  (.var primTyVar ↝ .bool) ↝ .var primTyVar

theorem eqName_ne_selectName : eqName ≠ selectName := by
  decide

/-- Look up a name in a constant association list (first match wins). -/
def ConstTable.lookup (cs : List (Name × Ty)) (n : Name) : Option Ty :=
  match cs with
  | [] => none
  | (m, ty) :: rest => if m = n then some ty else ConstTable.lookup rest n

@[simp] theorem ConstTable.lookup_nil (n : Name) : ConstTable.lookup [] n = none := rfl

@[simp] theorem ConstTable.lookup_cons_self (n : Name) (ty : Ty) (rest : List (Name × Ty)) :
    ConstTable.lookup ((n, ty) :: rest) n = some ty := by
  simp [ConstTable.lookup]

theorem ConstTable.lookup_cons_of_ne {n m : Name} (ty : Ty) (rest : List (Name × Ty))
    (h : m ≠ n) :
    ConstTable.lookup ((m, ty) :: rest) n = ConstTable.lookup rest n := by
  simp [ConstTable.lookup, h]

/-- Initial constant table: `eq` and `select`. -/
def holConstants : List (Name × Ty) :=
  [(eqName, eqTy), (selectName, selectTy)]

@[simp] theorem holConstants_eq : ConstTable.lookup holConstants eqName = some eqTy := by
  simp [holConstants, ConstTable.lookup]

@[simp] theorem holConstants_select : ConstTable.lookup holConstants selectName = some selectTy := by
  simp [holConstants, ConstTable.lookup, eqName_ne_selectName]

theorem holConstants_of_ne {n : Name} (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    ConstTable.lookup holConstants n = none := by
  simp [holConstants, ConstTable.lookup, heq.symm, hsel.symm]

theorem eqTy_instantiates (α : Ty) :
    eqTy.instantiates (α ↝ α ↝ .bool) :=
  ⟨[(primTyVar, α)], by simp [eqTy, primTyVar, Ty.inst, TySubst.lookup]⟩

theorem selectTy_instantiates (α : Ty) :
    selectTy.instantiates ((α ↝ .bool) ↝ α) :=
  ⟨[(primTyVar, α)], by simp [selectTy, primTyVar, Ty.inst, TySubst.lookup]⟩

end HOLean
