/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Elab.Term
import HOLean.Elab.Command
import HOLean.Axiom

/-!
Compile-time checks for the HOL elaborator.  Each `example` is `rfl` after
Lean elaborates the surface syntax and we translate it to `Ty` / `Tm`.
-/

namespace HOLean.Elab.Tests

open HOLean

/-! ## Types -/

example : hol_ty(Prop) = Ty.bool := rfl
example : hol_ty(Bool) = Ty.bool := rfl
example : hol_ty(Nat) = Ty.ind := rfl
example : hol_ty(Ind) = Ty.ind := rfl
example : hol_ty(Nat → Nat) = Ty.ind ↝ Ty.ind := rfl
example : hol_ty(Nat → Prop) = Ty.ind ↝ Ty.bool := rfl
example : hol_ty(Prop → Prop) = Ty.bool ↝ Ty.bool := rfl
example : hol_ty(α → α) = Ty.var "α" ↝ Ty.var "α" := rfl
example : hol_ty((α → β) → α → β) =
    ((Ty.var "α" ↝ Ty.var "β") ↝ Ty.var "α" ↝ Ty.var "β") := rfl

/-! ## Terms -/

example : hol_tm(fun (x : Nat) => x) = Tm.lam .ind (.bvar 0) := rfl
example : hol_tm(fun (p : Bool) => p) = Tm.lam .bool (.bvar 0) := rfl
example : hol_tm(fun (p : Prop) => p) = Tm.lam .bool (.bvar 0) := rfl
example : hol_tm((id : Nat → Nat)) = Tm.lam .ind (.bvar 0) := rfl
example : hol_tm(fun (f : Nat → Nat) (x : Nat) => f x) =
    Tm.lam (Ty.ind ↝ Ty.ind) (Tm.lam .ind (Tm.app (.bvar 1) (.bvar 0))) := rfl

/-! ## Propositions / boolean terms -/

example : hol_prop(True) = Tm.tru := rfl
example : hol_prop(False) = Tm.falsum := rfl
example : hol_prop(True ∧ False) = Tm.and Tm.tru Tm.falsum := rfl
example : hol_prop(True ∨ False) = Tm.or Tm.tru Tm.falsum := rfl
example : hol_prop(¬True) = Tm.not Tm.tru := rfl
example : hol_prop(True → False) = Tm.imp Tm.tru Tm.falsum := rfl
example : hol_prop(True = True) = Tm.mkEq .bool Tm.tru Tm.tru := rfl
example : hol_prop(True ↔ False) = Tm.mkEq .bool Tm.tru Tm.falsum := rfl

example : hol_prop(∀ x : Nat, x = x) =
    Tm.all .ind (Tm.lam .ind (Tm.mkEq .ind (.bvar 0) (.bvar 0))) := rfl

example : hol_prop(∃ x : Nat, x = x) =
    Tm.ex .ind (Tm.lam .ind (Tm.mkEq .ind (.bvar 0) (.bvar 0))) := rfl

example : hol_prop(∀ {α : Type} (x : α), x = x) =
    Tm.all (Ty.var "α") (Tm.lam (Ty.var "α") (Tm.mkEq (Ty.var "α") (.bvar 0) (.bvar 0))) :=
  rfl

example : hol_tm(fun (x : Nat) => x = x) =
    Tm.lam .ind (Tm.mkEq .ind (.bvar 0) (.bvar 0)) := rfl

example : hol_tm(true) = Tm.tru := rfl
example : hol_tm(fun (p : Bool) => !p) =
    Tm.lam .bool (Tm.not (.bvar 0)) := rfl

example : hol_tm(Classical.epsilon (fun _x : Nat => True)) =
    Tm.app (Tm.selectConst .ind) (Tm.lam .ind Tm.tru) := rfl

example : hol_prop(∃ f : Nat → Nat, oneOne f ∧ ¬ onto f) =
    Tm.ex (Ty.ind ↝ Ty.ind)
      (.lam (Ty.ind ↝ Ty.ind)
        ((Tm.oneOne .ind .ind (.bvar 0)).and
          (Tm.onto .ind .ind (.bvar 0)).not)) := rfl

/-! ## Sort dispatch (`hol(·)`) and the tight `%` form -/

example : hol(Prop) = Ty.bool := rfl
example : hol(True) = Tm.tru := rfl
example : hol(fun (x : Nat) => x) = Tm.lam .ind (.bvar 0) := rfl

example : hol_ty% Prop = Ty.bool := rfl
example : hol_prop% True = Tm.tru := rfl
example : hol_tm% true = Tm.tru := rfl

/-! ## Local context -/

variable {α : Type} (x : α)

example : hol_ty(α → α) = Ty.var "α" ↝ Ty.var "α" := rfl
example : hol_tm(x) = Tm.fvar "x" (Ty.var "α") := rfl
example : hol_tm(fun (_y : α) => x) = Tm.lam (Ty.var "α") (Tm.fvar "x" (Ty.var "α")) :=
  rfl

/-! ## Infer after translation -/

example : (hol_tm(fun (x : Nat) => x)).infer holEnv [] =
    some (hol_ty(Nat → Nat)) := rfl

example : (hol_prop(∀ x : Nat, x = x)).infer holEnv [] = some .bool := rfl

example : (hol_tm(fun (x : Nat) => x = x)).infer holEnv [] =
    some (Ty.ind ↝ Ty.bool) := rfl

/-! ## Dependent types are rejected (sort of the Π-body is `Type`) -/

/--
error: HOLean: dependent type is not a HOL type
  (n : Nat) → Fin (n + 1)
-/
#guard_msgs in
#check hol_ty(∀ n : Nat, Fin (n + 1))

/--
error: HOLean: expected a HOL type, but this is a proposition (use `hol_prop%`)
-/
#guard_msgs in
#check hol_ty(True)

/--
error: HOLean: expected a HOL term, but this is a type (use `hol_ty%`)
-/
#guard_msgs in
#check hol_tm(Nat)

/--
info: HOL type:
  HOLean.Ty.bool
-/
#guard_msgs in
#hol Prop

/--
info: HOL proposition:
  HOLean.Tm.const "tru" (HOLean.Ty.bool)
infer: some (HOLean.Ty.bool)
-/
#guard_msgs in
#hol True

/-! ## `hdef` / `htheorem` -/

section HDef
open HOLean.Elab
open Hol

hdef myId := fun {A : Type} (x : A) => x

hdef myNot : Prop → Prop := fun (p : Prop) => p → False

variable (n : Nat)

example : hol_tm(myId n) =
    Tm.app (Tm.const "myId" (Ty.ind ↝ Ty.ind)) (Tm.fvar "n" .ind) := rfl

example : hol_tm(myNot) = Tm.const "myNot" (.bool ↝ .bool) := rfl

example : hol_prop(myNot True) =
    Tm.app (Tm.const "myNot" (.bool ↝ .bool)) Tm.tru := rfl

/--
info: HOL term:
  HOLean.Tm.const "myNot" (HOLean.Ty.arrow (HOLean.Ty.bool) (HOLean.Ty.bool))
infer: some (HOLean.Ty.arrow (HOLean.Ty.bool) (HOLean.Ty.bool))
-/
#guard_msgs in
#hol myNot

/--
error: HOLean: constant `eq` is already declared
-/
#guard_msgs in
hdef eq : Prop → Prop → Prop := fun (p q : Prop) => p = q

htheorem true_eq_true : True = True :=
  Hol.refl (hol_tm(True))

htheorem tru_intro : True :=
  Hol.truth

example : true_eq_true.concl = Tm.mkEq .bool Tm.tru Tm.tru := rfl
example : tru_intro.concl = Tm.tru := rfl

htheorem tru_intro_again : True :=
  Hol.thm "tru_intro"

end HDef

end HOLean.Elab.Tests
