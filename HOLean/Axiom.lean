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
against `holLogic` (primitive constants plus defined connectives) so that
installing them does not depend on `holEnv` itself.

Infinity is an *existential* sentence.  We deliberately do **not** add an
`indSuc` constant.  A named witness is `Env.addConst` plus axioms — the same
mechanism as `addDef`, used later.

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

/-- A (closed, boolean) formula is a HOL axiom instance, typed in `holLogic`. -/
inductive HOLAxiom : Tm → Prop where
  | eta {α β f} (hf : HasType holLogic [] f (α ↝ β)) :
      HOLAxiom (etaAxiom α β f)
  /-- Locally closed instance: `HasType holLogic []` allows fvars, not dangling
  `bvar`s.  Open a bound predicate to an fvar before forming an axiom
  instance. -/
  | select {α P x}
      (hP : HasType holLogic [] P (α ↝ .bool))
      (hx : HasType holLogic [] x α) :
      HOLAxiom (selectAxiom α P x)
  | infinity : HOLAxiom infinityAxiom

/-- Initial HOL environment: defined connectives plus the primitive schemas. -/
def holEnv : Env where
  constants := holLogic.constants
  axioms := fun t => holLogic.axioms t ∨ HOLAxiom t

instance : Env.HasEq holEnv where
  eq_const := Env.HasEq.eq_const (env := holLogic)

instance : Env.HasSelect holEnv where
  select_const := Env.HasSelect.select_const (env := holLogic)

instance : Env.HasPrims holEnv where

instance : Env.HasConnectives holEnv where
  tru_const := Env.HasConnectives.tru_const (env := holLogic)
  and_const := Env.HasConnectives.and_const (env := holLogic)
  imp_const := Env.HasConnectives.imp_const (env := holLogic)
  all_const := Env.HasConnectives.all_const (env := holLogic)
  falsum_const := Env.HasConnectives.falsum_const (env := holLogic)
  not_const := Env.HasConnectives.not_const (env := holLogic)
  or_const := Env.HasConnectives.or_const (env := holLogic)
  ex_const := Env.HasConnectives.ex_const (env := holLogic)
  oneOne_const := Env.HasConnectives.oneOne_const (env := holLogic)
  onto_const := Env.HasConnectives.onto_const (env := holLogic)
  tru_ax := Or.inl (Env.HasConnectives.tru_ax (env := holLogic))
  and_ax := Or.inl (Env.HasConnectives.and_ax (env := holLogic))
  imp_ax := Or.inl (Env.HasConnectives.imp_ax (env := holLogic))
  all_ax := Or.inl (Env.HasConnectives.all_ax (env := holLogic))
  falsum_ax := Or.inl (Env.HasConnectives.falsum_ax (env := holLogic))
  not_ax := Or.inl (Env.HasConnectives.not_ax (env := holLogic))
  or_ax := Or.inl (Env.HasConnectives.or_ax (env := holLogic))
  ex_ax := Or.inl (Env.HasConnectives.ex_ax (env := holLogic))
  oneOne_ax := Or.inl (Env.HasConnectives.oneOne_ax (env := holLogic))
  onto_ax := Or.inl (Env.HasConnectives.onto_ax (env := holLogic))

theorem holLogic_le_holEnv : holLogic.LE holEnv :=
  ⟨fun _ _ h => h, fun _ h => Or.inl h⟩

theorem holCore_le_holEnv : holCore.LE holEnv :=
  holCore_le_holLogic.trans holLogic_le_holEnv

variable {env : Env}

theorem HasType.etaAxiom [Env.HasEq env] {Γ α β f} (hf : HasType env Γ f (α ↝ β)) :
    HasType env Γ (etaAxiom α β f) .bool :=
  HasType.mkEq
    (HasType.lam (HasType.app (hf.shift0 _) (HasType.bvar (by simp))))
    hf

theorem HasType.selectAxiom [Env.HasConnectives env] {Γ α P x}
    (hP : HasType env Γ P (α ↝ .bool)) (hx : HasType env Γ x α) :
    HasType env Γ (selectAxiom α P x) .bool :=
  HasType.imp (HasType.app hP hx)
    (HasType.app hP (HasType.app (HasType.selectConst α) hP))

theorem HasType.of_infinityAxiom [Env.HasConnectives env] :
    HasType env [] infinityAxiom .bool :=
  HasType.ex <|
    HasType.lam <|
      HasType.and
        (HasType.oneOne (HasType.bvar (by simp)))
        (HasType.not (HasType.onto (HasType.bvar (by simp))))

theorem HOLAxiom.bool_typed {p} (h : HOLAxiom p) : HasType holLogic [] p .bool := by
  cases h with
  | eta hf => exact HasType.etaAxiom hf
  | select hP hx => exact HasType.selectAxiom hP hx
  | infinity => exact HasType.of_infinityAxiom

theorem holEnv_WF : holEnv.WF := fun p hp =>
  match hp with
  | Or.inl h => (holLogic_WF p h).weakenEnv holLogic_le_holEnv
  | Or.inr h => (HOLAxiom.bool_typed h).weakenEnv holLogic_le_holEnv

theorem Provable.hol_ax {p} (h : HOLAxiom p) : [] ⊩[holEnv] p :=
  of_axiom holEnv_WF (Or.inr h)

end HOLean
