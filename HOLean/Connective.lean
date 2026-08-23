/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Typing

/-!
# Defined logical connectives

HOL Light defines the remaining connectives from equality (Harrison / Andrews).
These are *term formers* in Lean, not object-language constants — we are not
yet doing definitional extension of a signature.

When a former places an argument under a binder it `shift`s that argument, so
the formers are capture-avoiding on open terms.

```
T          ≔  (λ p. p) = (λ p. p)
p ∧ q      ≔  (λ f. f p q) = (λ f. f T T)
p ⇒ q      ≔  (p ∧ q) = p
∀ P        ≔  P = (λ x. T)
⊥          ≔  ∀ p. p
¬ p        ≔  p ⇒ ⊥
p ∨ q      ≔  ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
∃ P        ≔  ∀ q. (∀ x. P x ⇒ q) ⇒ q
ONE_ONE f  ≔  ∀ x y. f x = f y ⇒ x = y
ONTO f     ≔  ∀ y. ∃ x. y = f x
```
-/

namespace HOLean
namespace Tm

/-- Object-logic truth. -/
def tru : Tm :=
  mkEq (.bool ↝ .bool) (.lam .bool (.bvar 0)) (.lam .bool (.bvar 0))

/-- The type of a binary boolean combinator, used to define conjunction. -/
def boolCombTy : Ty :=
  .bool ↝ .bool ↝ .bool

theorem boolCombTy_eq : boolCombTy = (.bool ↝ .bool ↝ .bool) := rfl

/-- Object-logic conjunction. -/
def and (p q : Tm) : Tm :=
  mkEq (boolCombTy ↝ .bool)
    (.lam boolCombTy (.app (.app (.bvar 0) (p.shift 1 0)) (q.shift 1 0)))
    (.lam boolCombTy (.app (.app (.bvar 0) (tru.shift 1 0)) (tru.shift 1 0)))

/-- Object-logic implication `p ⇒ q`, defined as `(p ∧ q) = p`. -/
def imp (p q : Tm) : Tm :=
  mkEq .bool (p.and q) p

/-- Universal quantification of a predicate `P : α ↝ bool`. -/
def all (α : Ty) (P : Tm) : Tm :=
  mkEq (α ↝ .bool) P (.lam α tru)

/-- `∀ p. p`. -/
def falsum : Tm :=
  all .bool (.lam .bool (.bvar 0))

/-- Negation. -/
def not (p : Tm) : Tm :=
  p.imp falsum

/-- Disjunction via the second-order encoding. -/
def or (p q : Tm) : Tm :=
  all .bool
    (.lam .bool
      ((p.shift 1 0).imp (.bvar 0) |>.imp ((q.shift 1 0).imp (.bvar 0) |>.imp (.bvar 0))))

/-- Existential quantification of a predicate `P : α ↝ bool`. -/
def ex (α : Ty) (P : Tm) : Tm :=
  all .bool
    (.lam .bool
      ((all α (.lam α
        (((P.shift 1 0).shift 1 0).app (.bvar 0) |>.imp (.bvar 1)))).imp (.bvar 0)))

/-- Injectivity of `f : α ↝ β`. -/
def oneOne (α β : Ty) (f : Tm) : Tm :=
  all α
    (.lam α
      (all α
        (.lam α
          ((mkEq β (((f.shift 1 0).shift 1 0).app (.bvar 1))
              (((f.shift 1 0).shift 1 0).app (.bvar 0))).imp
            (mkEq α (.bvar 1) (.bvar 0))))))

/-- Surjectivity of `f : α ↝ β`. -/
def onto (α β : Ty) (f : Tm) : Tm :=
  all β
    (.lam β
      (ex α
        (.lam α (mkEq β (.bvar 1) (((f.shift 1 0).shift 1 0).app (.bvar 0))))))

theorem tru_LC : tru.LC 0 = true := rfl

theorem tru_not_free (x : Name) (α : Ty) : tru.freeIn x α = false := rfl

end Tm

variable {env : Env} [Env.HasEq env]

theorem HasType.tru {Γ} : HasType env Γ Tm.tru .bool :=
  HasType.mkEq
    (HasType.lam (HasType.bvar (by simp)))
    (HasType.lam (HasType.bvar (by simp)))

theorem HasType.and {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.and q) .bool := by
  unfold Tm.and Tm.boolCombTy
  apply HasType.mkEq
  · apply HasType.lam
    exact HasType.app
      (HasType.app (HasType.bvar (by simp)) (hp.shift0 _))
      (hq.shift0 _)
  · apply HasType.lam
    exact HasType.app
      (HasType.app (HasType.bvar (by simp)) (HasType.tru.shift0 _))
      (HasType.tru.shift0 _)

theorem HasType.imp {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.imp q) .bool :=
  HasType.mkEq (HasType.and hp hq) hp

theorem HasType.all {Γ α P} (hP : HasType env Γ P (α ↝ .bool)) :
    HasType env Γ (Tm.all α P) .bool :=
  HasType.mkEq hP (HasType.lam HasType.tru)

theorem HasType.falsum {Γ} : HasType env Γ Tm.falsum .bool :=
  HasType.all (HasType.lam (HasType.bvar (by simp)))

theorem HasType.not {Γ p} (hp : HasType env Γ p .bool) :
    HasType env Γ p.not .bool :=
  HasType.imp hp HasType.falsum

theorem HasType.or {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.or q) .bool := by
  unfold Tm.or
  apply HasType.all
  apply HasType.lam
  refine HasType.imp (HasType.imp (hp.shift0 _) (HasType.bvar (by simp))) ?_
  refine HasType.imp (HasType.imp (hq.shift0 _) (HasType.bvar (by simp))) ?_
  exact HasType.bvar (by simp)

theorem HasType.ex {Γ α P} (hP : HasType env Γ P (α ↝ .bool)) :
    HasType env Γ (Tm.ex α P) .bool := by
  unfold Tm.ex
  apply HasType.all
  apply HasType.lam
  refine HasType.imp ?_ (HasType.bvar (by simp))
  apply HasType.all
  apply HasType.lam
  refine HasType.imp ?_ (HasType.bvar (by simp))
  exact HasType.app (hP.shift_at .bool 0 |>.shift_at α 0) (HasType.bvar (by simp))

theorem HasType.oneOne {Γ α β f} (hf : HasType env Γ f (α ↝ β)) :
    HasType env Γ (Tm.oneOne α β f) .bool := by
  unfold Tm.oneOne
  apply HasType.all
  apply HasType.lam
  apply HasType.all
  apply HasType.lam
  refine HasType.imp ?_ (HasType.mkEq (HasType.bvar (by simp))
    (HasType.bvar (by simp)))
  refine HasType.mkEq ?_ ?_
  · exact HasType.app (hf.shift_at α 0 |>.shift_at α 0) (HasType.bvar (by simp))
  · exact HasType.app (hf.shift_at α 0 |>.shift_at α 0) (HasType.bvar (by simp))

theorem HasType.onto {Γ α β f} (hf : HasType env Γ f (α ↝ β)) :
    HasType env Γ (Tm.onto α β f) .bool := by
  unfold Tm.onto
  apply HasType.all
  apply HasType.lam
  apply HasType.ex
  apply HasType.lam
  refine HasType.mkEq (HasType.bvar (by simp)) ?_
  exact HasType.app (hf.shift_at β 0 |>.shift_at α 0) (HasType.bvar (by simp))

end HOLean
