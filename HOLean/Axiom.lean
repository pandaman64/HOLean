/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Connective
import HOLean.Kernel

/-!
# HOL axiom schemas

The ten kernel rules are the *inference* system.  Full HOL Light additionally
postulates:

* **ETA** — `⊢ (λ x. f x) = f` (gives functional extensionality with the kernel)
* **SELECT** — Hilbert choice, `⊢ P x ⇒ P (ε P)`
* **INFINITY** — `ind` is Dedekind-infinite

Infinity is recorded as a comment until `ONE_ONE` / `ONTO` are defined from the
connectives.  The two schemas below are already well-typed closed booleans.
-/

namespace HOLean

/-- `η`: `(λ x. f x) = f` for a closed function `f`. -/
def etaAxiom (α β : Ty) (f : Tm) : Tm :=
  Tm.mkEq (α ↝ β) (.lam α (.app f (.bvar 0))) f

/-- Hilbert choice: `P x ⇒ P (ε P)`. -/
def selectAxiom (α : Ty) (P x : Tm) : Tm :=
  Tm.imp (.app P x) (.app P (.app (.const .select α) P))

/-- A (closed, boolean) formula is a HOL axiom instance. -/
inductive IsHOLAxiom : Tm → Prop where
  | eta {α β f} (hf : HasType [] f (α ↝ β)) :
      IsHOLAxiom (etaAxiom α β f)
  | select {α P x}
      (hP : HasType [] P (α ↝ .bool))
      (hx : HasType [] x α) :
      IsHOLAxiom (selectAxiom α P x)

theorem HasType.etaAxiom {α β f} (hf : HasType [] f (α ↝ β)) :
    HasType [] (etaAxiom α β f) .bool :=
  HasType.mkEq
    (HasType.lam (HasType.app hf.of_closed (HasType.bvar (by simp [Ctx.get]))))
    hf

theorem HasType.selectAxiom {α P x}
    (hP : HasType [] P (α ↝ .bool)) (hx : HasType [] x α) :
    HasType [] (selectAxiom α P x) .bool :=
  HasType.imp (HasType.app hP hx)
    (HasType.app hP (HasType.app HasType.const hP))

theorem IsHOLAxiom.bool_typed {p} (h : IsHOLAxiom p) : HasType [] p .bool := by
  cases h with
  | eta hf => exact HasType.etaAxiom hf
  | select hP hx => exact HasType.selectAxiom hP hx

/-- Kernel theorems plus the HOL axiom schemas.  Soundness of this predicate
is the target of the eventual `ZFSet` model. -/
inductive Proves : List Tm → Tm → Prop where
  | kernel {Γ p} : Provable Γ p → Proves Γ p
  | axiom {p} : IsHOLAxiom p → Proves [] p

theorem Proves.bool_typed {Γ p} (h : Proves Γ p) :
    (∀ q ∈ Γ, HasType [] q .bool) ∧ HasType [] p .bool := by
  cases h with
  | kernel hk => exact hk.bool_typed
  | axiom ha => exact ⟨by intro q hq; cases hq, ha.bool_typed⟩

end HOLean
