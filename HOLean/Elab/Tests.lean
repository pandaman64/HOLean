/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Elab.Term

/-!
Compile-time checks for the HOL elaborator.  Each `example` is `rfl` after
Lean elaborates the surface syntax and we translate it to `Ty` / `Tm`.
-/

namespace HOLean.Elab.Tests

open HOLean

/-! ## Types -/

example : hol_ty% Prop = Ty.bool := rfl
example : hol_ty% Bool = Ty.bool := rfl
example : hol_ty% Nat = Ty.ind := rfl
example : hol_ty% Ind = Ty.ind := rfl
example : hol_ty% (Nat → Nat) = Ty.ind ↝ Ty.ind := rfl
example : hol_ty% (Nat → Prop) = Ty.ind ↝ Ty.bool := rfl
example : hol_ty% (Prop → Prop) = Ty.bool ↝ Ty.bool := rfl
example : hol_ty% (α → α) = Ty.var "α" ↝ Ty.var "α" := rfl
example : hol_ty% ((α → β) → α → β) =
    ((Ty.var "α" ↝ Ty.var "β") ↝ Ty.var "α" ↝ Ty.var "β") := rfl

/-! ## Terms -/

example : hol_tm% (fun (x : Nat) => x) = Tm.lam .ind (.bvar 0) := rfl
example : hol_tm% (fun (p : Bool) => p) = Tm.lam .bool (.bvar 0) := rfl
example : hol_tm% (fun (p : Prop) => p) = Tm.lam .bool (.bvar 0) := rfl
example : hol_tm% (id : Nat → Nat) = Tm.lam .ind (.bvar 0) := rfl
example : hol_tm% (fun (f : Nat → Nat) (x : Nat) => f x) =
    Tm.lam (Ty.ind ↝ Ty.ind) (Tm.lam .ind (Tm.app (.bvar 1) (.bvar 0))) := rfl

/-! ## Propositions / boolean terms -/

example : hol_prop% True = Tm.tru := rfl
example : hol_prop% False = Tm.falsum := rfl
example : hol_prop% (True ∧ False) = Tm.and Tm.tru Tm.falsum := rfl
example : hol_prop% (True ∨ False) = Tm.or Tm.tru Tm.falsum := rfl
example : hol_prop% ¬True = Tm.not Tm.tru := rfl
example : hol_prop% (True → False) = Tm.imp Tm.tru Tm.falsum := rfl
example : hol_prop% (True = True) = Tm.mkEq .bool Tm.tru Tm.tru := rfl
example : hol_prop% (True ↔ False) = Tm.mkEq .bool Tm.tru Tm.falsum := rfl

example : hol_prop% (∀ x : Nat, x = x) =
    Tm.all .ind (Tm.lam .ind (Tm.mkEq .ind (.bvar 0) (.bvar 0))) := rfl

example : hol_prop% (∃ x : Nat, x = x) =
    Tm.ex .ind (Tm.lam .ind (Tm.mkEq .ind (.bvar 0) (.bvar 0))) := rfl

example : hol_prop% (∀ {α : Type} (x : α), x = x) =
    Tm.all (Ty.var "α") (Tm.lam (Ty.var "α") (Tm.mkEq (Ty.var "α") (.bvar 0) (.bvar 0))) :=
  rfl

example : hol_tm% (fun (x : Nat) => x = x) =
    Tm.lam .ind (Tm.mkEq .ind (.bvar 0) (.bvar 0)) := rfl

example : hol_tm% true = Tm.tru := rfl
example : hol_tm% (fun (p : Bool) => !p) =
    Tm.lam .bool (Tm.not (.bvar 0)) := rfl

/-! ## Sort dispatch (`hol%`) -/

example : hol% Prop = Ty.bool := rfl
example : hol% True = Tm.tru := rfl
example : hol% (fun (x : Nat) => x) = Tm.lam .ind (.bvar 0) := rfl

/-! ## Local context -/

variable {α : Type} (x : α)

example : hol_ty% (α → α) = Ty.var "α" ↝ Ty.var "α" := rfl
example : hol_tm% x = Tm.fvar "x" (Ty.var "α") := rfl
example : hol_tm% (fun (y : α) => x) = Tm.lam (Ty.var "α") (Tm.fvar "x" (Ty.var "α")) :=
  rfl

/-! ## Infer after translation -/

example : (hol_tm% (fun (x : Nat) => x)).infer holEnv [] =
    some (hol_ty% (Nat → Nat)) := rfl

example : (hol_prop% (∀ x : Nat, x = x)).infer holEnv [] = some .bool := rfl

example : (hol_tm% (fun (x : Nat) => x = x)).infer holEnv [] =
    some (Ty.ind ↝ Ty.bool) := rfl

end HOLean.Elab.Tests
