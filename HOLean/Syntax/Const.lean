/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Ty

/-!
# Primitive constants

The HOL Light kernel starts with equality alone; Hilbert choice is added as a
second primitive.  Every other logical constant is a definitional extension.

Each primitive is *parametric* in a single type argument `α`.
-/

namespace HOLean

/-- Primitive (non-defined) HOL constants. -/
inductive Const where
  /-- Equality, with generic type `α ↝ α ↝ bool`. -/
  | eq
  /-- Hilbert ε / `@`, with generic type `(α ↝ bool) ↝ α`. -/
  | select
  deriving DecidableEq, Repr, Inhabited

namespace Const

/-- The type of a primitive constant after instantiating its unique type
parameter. -/
def inst : Const → Ty → Ty
  | eq, α => α ↝ α ↝ .bool
  | select, α => (α ↝ .bool) ↝ α

@[simp] theorem inst_eq (α : Ty) : eq.inst α = (α ↝ α ↝ .bool) := rfl
@[simp] theorem inst_select (α : Ty) : select.inst α = ((α ↝ .bool) ↝ α) := rfl

/-- Type instantiation commutes with reading off a constant's type. -/
theorem inst_tyInst (c : Const) (α : Ty) (θ : TySubst) :
    (c.inst α).inst θ = c.inst (α.inst θ) := by
  cases c <;> simp [inst, Ty.inst]

end Const

end HOLean
