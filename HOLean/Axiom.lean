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
* **INFINITY** — `ind` is Dedekind-infinite:
  `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`

Infinity is an *existential* sentence in the existing language `{eq, select}`.
We deliberately do **not** add an `indSuc` constant.  That would be a
signature extension (an environment), which is the same mechanism as
`new_basic_definition` — deferred until the tradeoffs are settled.

See the README section “Environments vs definitional extensions”.
-/

namespace HOLean

/-- `η`: `(λ x. f x) = f`.  `f` is shifted under the binder so the former is
capture-avoiding on open terms. -/
def etaAxiom (α β : Ty) (f : Tm) : Tm :=
  Tm.mkEq (α ↝ β) (.lam α (.app (f.shift 1 0) (.bvar 0))) f

/-- Hilbert choice: `P x ⇒ P (ε P)`.

Neither `imp` nor `app` binds, so this former is already well-formed when `P`
or `x` is a `bvar` (a predicate/witness under a local binder).  Axiom
*instances* (`IsHOLAxiom`) still require a locally closed sentence: theorems
cannot mention dangling indices.  To use `ε` on a bound predicate, open it as
an `fvar`, instantiate the schema, then abstract — the usual locally nameless
discipline. -/
def selectAxiom (α : Ty) (P x : Tm) : Tm :=
  Tm.imp (.app P x) (.app P (.app (.const .select α) P))

/-- `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`. -/
def infinityAxiom : Tm :=
  Tm.ex (Ty.ind ↝ Ty.ind)
    (.lam (Ty.ind ↝ Ty.ind)
      ((Tm.oneOne .ind .ind (.bvar 0)).and
        (Tm.onto .ind .ind (.bvar 0)).not))

/-- A (closed, boolean) formula is a HOL axiom instance. -/
inductive IsHOLAxiom : Tm → Prop where
  | eta {α β f} (hf : HasType [] f (α ↝ β)) :
      IsHOLAxiom (etaAxiom α β f)
  /-- Locally closed instance: `HasType []` allows fvars, not dangling `bvar`s.
  Open a bound predicate to an fvar before forming an axiom instance. -/
  | select {α P x}
      (hP : HasType [] P (α ↝ .bool))
      (hx : HasType [] x α) :
      IsHOLAxiom (selectAxiom α P x)
  | infinity : IsHOLAxiom infinityAxiom

theorem HasType.etaAxiom {Γ α β f} (hf : HasType Γ f (α ↝ β)) :
    HasType Γ (etaAxiom α β f) .bool :=
  HasType.mkEq
    (HasType.lam (HasType.app (hf.shift0 _) (HasType.bvar (by simp))))
    hf

theorem HasType.selectAxiom {Γ α P x}
    (hP : HasType Γ P (α ↝ .bool)) (hx : HasType Γ x α) :
    HasType Γ (selectAxiom α P x) .bool :=
  HasType.imp (HasType.app hP hx)
    (HasType.app hP (HasType.app (HasType.const .select α) hP))

theorem HasType.of_infinityAxiom : HasType [] infinityAxiom .bool :=
  HasType.ex <|
    HasType.lam <|
      HasType.and
        (HasType.oneOne (HasType.bvar (by simp)))
        (HasType.not (HasType.onto (HasType.bvar (by simp))))

theorem IsHOLAxiom.bool_typed {p} (h : IsHOLAxiom p) : HasType [] p .bool := by
  cases h with
  | eta hf => exact HasType.etaAxiom hf
  | select hP hx => exact HasType.selectAxiom hP hx
  | infinity => exact HasType.of_infinityAxiom

/-- Kernel theorems plus the HOL axiom schemas.  Soundness of this predicate
is the target of the eventual `ZFSet` model. -/
inductive Proves : List Tm → Tm → Prop where
  | kernel {Γ p} : Provable Γ p → Proves Γ p
  | ax {p} : IsHOLAxiom p → Proves [] p

theorem Proves.bool_typed {Γ p} (h : Proves Γ p) :
    (∀ q ∈ Γ, HasType [] q .bool) ∧ HasType [] p .bool := by
  cases h with
  | kernel hk => exact hk.bool_typed
  | ax ha =>
    constructor
    · intro q hq; cases hq
    · exact ha.bool_typed

end HOLean
