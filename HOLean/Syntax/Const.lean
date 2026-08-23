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
substitution instance of the generic type (`Ty.isInstanceOf`).
-/

namespace HOLean

/-- Name of object-logic equality. -/
def eqName : Name := "eq"

/-- Name of Hilbert ε / `@`. -/
def selectName : Name := "select"

/-- The schematic parameter of `eq` and `select`. -/
def primTyVar : Name := "A"

/-- Generic type of equality: `A ↝ A ↝ bool`. -/
def eqTy : Ty :=
  .var primTyVar ↝ .var primTyVar ↝ .bool

/-- Generic type of Hilbert choice: `(A ↝ bool) ↝ A`. -/
def selectTy : Ty :=
  (.var primTyVar ↝ .bool) ↝ .var primTyVar

theorem eqName_ne_selectName : eqName ≠ selectName := by
  decide

/-- Initial constant table: `eq` and `select`. -/
def holConstants (n : Name) : Option Ty :=
  if n = eqName then some eqTy
  else if n = selectName then some selectTy
  else none

@[simp] theorem holConstants_eq : holConstants eqName = some eqTy := by
  simp [holConstants]

@[simp] theorem holConstants_select : holConstants selectName = some selectTy := by
  simp [holConstants, show selectName ≠ eqName from eqName_ne_selectName.symm]

theorem eqTy_isInstanceOf (α : Ty) :
    eqTy.isInstanceOf (α ↝ α ↝ .bool) :=
  ⟨[(primTyVar, α)], by simp [eqTy, primTyVar, Ty.inst, TySubst.lookup]⟩

theorem selectTy_isInstanceOf (α : Ty) :
    selectTy.isInstanceOf ((α ↝ .bool) ↝ α) :=
  ⟨[(primTyVar, α)], by simp [selectTy, primTyVar, Ty.inst, TySubst.lookup]⟩

end HOLean
