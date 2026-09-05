/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Connective
import HOLean.Kernel
import HOLean.Elab.Term

/-!
# HOL axioms

The ten kernel rules are the *inference* system.  Full HOL Light additionally
postulates three closed sentences (after the connectives of `bool.ml` /
`holLogic`):

* **ETA** — `⊢ ∀ f. (λ x. f x) = f` (gives functional extensionality with the kernel)
* **SELECT** — Hilbert choice, `⊢ ∀ P x. P x ⇒ P (ε P)`
* **INFINITY** — `ind` is Dedekind-infinite:
  `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`

They are typed against `holLogic` (primitive constants plus defined
connectives) so that installing them does not depend on `holEnv` itself.

Infinity is an *existential* sentence.  We deliberately do **not** add an
`indSuc` constant.  A named witness is `Env.addConst` plus axioms — the same
mechanism as `addDef`, used later.

See the README section “Environments vs definitional extensions”.
-/

namespace HOLean

/-- `η`: `∀ f : A ↝ B. (λ x. f x) = f` with schematic type variables `A` and `B`. -/
def etaAxiom : Tm :=
  hol_prop(∀ {A B : Type} (f : A → B), (fun (x : A) => f x) = f)

theorem etaAxiom_eq :
    etaAxiom =
      Tm.all (.var primTyVar ↝ .var primTyVarB)
        (.lam (.var primTyVar ↝ .var primTyVarB)
          (Tm.mkEq (.var primTyVar ↝ .var primTyVarB)
            (.lam (.var primTyVar) (.app (.bvar 1) (.bvar 0)))
            (.bvar 0))) :=
  rfl

/-- Hilbert choice: `∀ P x. P x ⇒ P (ε P)` with schematic type variable `A`. -/
def selectAxiom : Tm :=
  hol_prop(∀ {A : Type} (P : A → Prop) (x : A), P x → P (select P))

theorem selectAxiom_eq :
    selectAxiom =
      Tm.all (.var primTyVar ↝ .bool)
        (.lam (.var primTyVar ↝ .bool)
          (Tm.all (.var primTyVar)
            (.lam (.var primTyVar)
              (Tm.imp (.app (.bvar 1) (.bvar 0))
                (.app (.bvar 1) (.app (Tm.selectConst (.var primTyVar)) (.bvar 1))))))) :=
  rfl

/-- `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`. -/
def infinityAxiom : Tm :=
  hol_prop(∃ f : Ind → Ind, oneOne f ∧ ¬ onto f)

theorem infinityAxiom_eq :
    infinityAxiom =
      Tm.ex (Ty.ind ↝ Ty.ind)
        (.lam (Ty.ind ↝ Ty.ind)
          ((Tm.oneOne .ind .ind (.bvar 0)).and
            (Tm.onto .ind .ind (.bvar 0)).not)) :=
  rfl

/-- The three closed HOL axiom sentences, typed in `holLogic`. -/
inductive HOLAxiom : Tm → Prop where
  | eta : HOLAxiom etaAxiom
  | select : HOLAxiom selectAxiom
  | infinity : HOLAxiom infinityAxiom

/-- Initial HOL environment: defined connectives plus the three axioms. -/
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

theorem HasType.of_etaAxiom [Env.HasConnectives env] :
    HasType env [] etaAxiom .bool := by
  rw [etaAxiom_eq]
  let A : Ty := .var primTyVar
  let B : Ty := .var primTyVarB
  have hb0A : HasType env [A, A ↝ B] (.bvar 0) A :=
    HasType.bvar List.getElem?_cons_zero
  have hb1 : HasType env [A, A ↝ B] (.bvar 1) (A ↝ B) :=
    HasType.bvar (by simp)
  have hb0F : HasType env [A ↝ B] (.bvar 0) (A ↝ B) :=
    HasType.bvar List.getElem?_cons_zero
  exact HasType.all <| HasType.lam <|
    HasType.mkEq (HasType.lam (HasType.app hb1 hb0A)) hb0F

theorem HasType.of_selectAxiom [Env.HasConnectives env] :
    HasType env [] selectAxiom .bool := by
  rw [selectAxiom_eq]
  let A : Ty := .var primTyVar
  have hb0 : HasType env [A, A ↝ .bool] (.bvar 0) A :=
    HasType.bvar List.getElem?_cons_zero
  have hb1 : HasType env [A, A ↝ .bool] (.bvar 1) (A ↝ .bool) :=
    HasType.bvar (by simp)
  exact HasType.all <| HasType.lam <| HasType.all <| HasType.lam <|
    HasType.imp (HasType.app hb1 hb0)
      (HasType.app hb1 (HasType.app (HasType.selectConst A) hb1))

theorem HasType.of_infinityAxiom [Env.HasConnectives env] :
    HasType env [] infinityAxiom .bool :=
  HasType.ex <|
    HasType.lam <|
      HasType.and
        (HasType.oneOne (HasType.bvar (by simp)))
        (HasType.not (HasType.onto (HasType.bvar (by simp))))

theorem HOLAxiom.bool_typed {p} (h : HOLAxiom p) : HasType holLogic [] p .bool := by
  cases h with
  | eta => exact HasType.of_etaAxiom
  | select => exact HasType.of_selectAxiom
  | infinity => exact HasType.of_infinityAxiom

theorem holEnv_WF : holEnv.WF := fun p hp =>
  match hp with
  | Or.inl h => (holLogic_WF p h).weakenEnv holLogic_le_holEnv
  | Or.inr h => (HOLAxiom.bool_typed h).weakenEnv holLogic_le_holEnv

theorem Provable.hol_ax {p} (h : HOLAxiom p) : [] ⊩[holEnv] p :=
  of_axiom holEnv_WF (Or.inr h)

end HOLean
