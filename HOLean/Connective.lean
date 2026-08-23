/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Typing

/-!
# Defined logical connectives

HOL Light defines the propositional connectives from equality alone
(Harrison / Andrews).  These are *term formers* in the object language, not
Lean connectives.

```
T      ≔  (λ p. p) = (λ p. p)
p ∧ q  ≔  (λ f. f p q) = (λ f. f T T)
p ⇒ q  ≔  (p ∧ q) = p
∀ P    ≔  P = (λ x. T)
```

Arguments of the binary connectives are required to be locally closed, matching
the kernel's convention that hypotheses are closed booleans.
-/

namespace HOLean
namespace Tm

/-- Object-logic truth. -/
def tru : Tm :=
  mkEq (.bool ↝ .bool) (.lam .bool (.bvar 0)) (.lam .bool (.bvar 0))

/-- The type of a binary boolean combinator, used to define conjunction. -/
def boolCombTy : Ty :=
  .bool ↝ .bool ↝ .bool

/-- Object-logic conjunction of two closed boolean terms. -/
def and (p q : Tm) : Tm :=
  mkEq (boolCombTy ↝ .bool)
    (.lam boolCombTy (.app (.app (.bvar 0) p) q))
    (.lam boolCombTy (.app (.app (.bvar 0) tru) tru))

/-- Object-logic implication `p ⇒ q`, defined as `(p ∧ q) = p`. -/
def imp (p q : Tm) : Tm :=
  mkEq .bool (p.and q) p

/-- Universal quantification: `∀ P` means `P = (λ x. T)`. -/
def all (α : Ty) (P : Tm) : Tm :=
  mkEq (α ↝ .bool) P (.lam α tru)

end Tm

theorem HasType.tru {Γ} : HasType Γ Tm.tru .bool :=
  HasType.mkEq
    (HasType.lam (HasType.bvar (by simp [Ctx.get])))
    (HasType.lam (HasType.bvar (by simp [Ctx.get])))

theorem HasType.and {p q}
    (hp : HasType [] p .bool) (hq : HasType [] q .bool) :
    HasType [] (p.and q) .bool := by
  unfold Tm.and Tm.boolCombTy
  apply HasType.mkEq
  · apply HasType.lam
    exact HasType.app
      (HasType.app (HasType.bvar (by simp [Ctx.get])) hp.of_closed)
      hq.of_closed
  · apply HasType.lam
    exact HasType.app
      (HasType.app (HasType.bvar (by simp [Ctx.get])) HasType.tru)
      HasType.tru

theorem HasType.imp {p q}
    (hp : HasType [] p .bool) (hq : HasType [] q .bool) :
    HasType [] (p.imp q) .bool :=
  HasType.mkEq (HasType.and hp hq) hp

theorem HasType.all {α P} (hP : HasType [] P (α ↝ .bool)) :
    HasType [] (Tm.all α P) .bool :=
  HasType.mkEq hP (HasType.lam HasType.tru)

end HOLean
