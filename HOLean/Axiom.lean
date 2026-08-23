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

These are the axioms of the initial environment `holEnv`.  They are typed
against `holCore` (same constants, no axioms) so that installing them does
not depend on `holEnv` itself.

Infinity is an *existential* sentence in the language `{eq, select}`.
We deliberately do **not** add an `indSuc` constant.  A named witness is
`Env.addConst` plus axioms — the same mechanism as `addDef`, used later.

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
*instances* (`HOLAxiom`) still require a locally closed sentence: theorems
cannot mention dangling indices.  To use `ε` on a bound predicate, open it as
an `fvar`, instantiate the schema, then abstract — the usual locally nameless
discipline. -/
def selectAxiom (α : Ty) (P x : Tm) : Tm :=
  Tm.imp (.app P x) (.app P (.app (Tm.selectConst α) P))

/-- `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`. -/
def infinityAxiom : Tm :=
  Tm.ex (Ty.ind ↝ Ty.ind)
    (.lam (Ty.ind ↝ Ty.ind)
      ((Tm.oneOne .ind .ind (.bvar 0)).and
        (Tm.onto .ind .ind (.bvar 0)).not))

/-- A (closed, boolean) formula is a HOL axiom instance, typed in `holCore`. -/
inductive HOLAxiom : Tm → Prop where
  | eta {α β f} (hf : HasType holCore [] f (α ↝ β)) :
      HOLAxiom (etaAxiom α β f)
  /-- Locally closed instance: `HasType holCore []` allows fvars, not dangling
  `bvar`s.  Open a bound predicate to an fvar before forming an axiom
  instance. -/
  | select {α P x}
      (hP : HasType holCore [] P (α ↝ .bool))
      (hx : HasType holCore [] x α) :
      HOLAxiom (selectAxiom α P x)
  | infinity : HOLAxiom infinityAxiom

/-- Initial HOL environment: primitive constants plus the axiom schemas. -/
def holEnv : Env where
  constants := holConstants
  axioms := HOLAxiom

instance : Env.HasEq holEnv where
  eq_const := holConstants_eq

instance : Env.HasSelect holEnv where
  select_const := holConstants_select

instance : Env.HasPrims holEnv where

theorem holCore_le_holEnv : holCore.LE holEnv :=
  ⟨fun _ _ h => h, fun _ h => False.elim h⟩

variable {env : Env}

theorem HasType.etaAxiom [Env.HasEq env] {Γ α β f} (hf : HasType env Γ f (α ↝ β)) :
    HasType env Γ (etaAxiom α β f) .bool :=
  HasType.mkEq
    (HasType.lam (HasType.app (hf.shift0 _) (HasType.bvar (by simp))))
    hf

theorem HasType.selectAxiom [Env.HasPrims env] {Γ α P x}
    (hP : HasType env Γ P (α ↝ .bool)) (hx : HasType env Γ x α) :
    HasType env Γ (selectAxiom α P x) .bool :=
  HasType.imp (HasType.app hP hx)
    (HasType.app hP (HasType.app (HasType.selectConst α) hP))

theorem HasType.of_infinityAxiom [Env.HasEq env] :
    HasType env [] infinityAxiom .bool :=
  HasType.ex <|
    HasType.lam <|
      HasType.and
        (HasType.oneOne (HasType.bvar (by simp)))
        (HasType.not (HasType.onto (HasType.bvar (by simp))))

theorem HOLAxiom.bool_typed {p} (h : HOLAxiom p) : HasType holCore [] p .bool := by
  cases h with
  | eta hf => exact HasType.etaAxiom hf
  | select hP hx => exact HasType.selectAxiom hP hx
  | infinity => exact HasType.of_infinityAxiom

theorem holEnv_WF : holEnv.WF := fun _ hp =>
  (HOLAxiom.bool_typed hp).weakenEnv holCore_le_holEnv

/-- Kernel theorems plus environment axioms.  Soundness of this predicate
is the target of the eventual `ZFSet` model. -/
inductive Proves (env : Env) : List Tm → Tm → Prop where
  | kernel {Γ p} : Provable env Γ p → Proves env Γ p
  | ax {p} (hp : env.axioms p) (hty : HasType env [] p .bool) : Proves env [] p

theorem Proves.weakenEnv {env env' : Env} {Γ p}
    (hle : env.LE env') (h : Proves env Γ p) : Proves env' Γ p := by
  cases h with
  | kernel hk => exact kernel (hk.weakenEnv hle)
  | ax hp hty => exact ax (hle.axioms _ hp) (hty.weakenEnv hle)

theorem Proves.hol_ax {p} (h : HOLAxiom p) : Proves holEnv [] p :=
  ax h (holEnv_WF _ h)

theorem Proves.bool_typed [Env.HasEq env] {Γ p} (h : Proves env Γ p) :
    (∀ q ∈ Γ, HasType env [] q .bool) ∧ HasType env [] p .bool := by
  cases h with
  | kernel hk => exact hk.bool_typed
  | ax _ hty =>
    constructor
    · intro q hq; cases hq
    · exact hty

/-- Abbreviation kept for existing references. -/
abbrev IsHOLAxiom := HOLAxiom

end HOLean
