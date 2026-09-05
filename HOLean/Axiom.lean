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

/-- Initial HOL environment: defined connectives plus the three closed axioms.
Axioms are prepended newest-first: `[infinityAxiom, selectAxiom, etaAxiom] ++
holLogic.axioms`. -/
def holEnv : Env :=
  ((holLogic.addAxiom etaAxiom).addAxiom selectAxiom).addAxiom infinityAxiom

instance : Env.HasEq holEnv where
  eq_const := Env.HasEq.eq_const (env := holLogic)

instance : Env.HasSelect holEnv where
  select_const := Env.HasSelect.select_const (env := holLogic)

instance : Env.HasPrims holEnv where

instance : Env.HasConnectives holEnv :=
  letI : Env.HasConnectives (holLogic.addAxiom etaAxiom) :=
    Env.HasConnectives.addAxiom etaAxiom
  letI : Env.HasConnectives ((holLogic.addAxiom etaAxiom).addAxiom selectAxiom) :=
    Env.HasConnectives.addAxiom selectAxiom
  Env.HasConnectives.addAxiom infinityAxiom

theorem holLogic_le_holEnv : holLogic.LE holEnv :=
  (Env.LE.addAxiom holLogic etaAxiom).trans
    ((Env.LE.addAxiom _ selectAxiom).trans (Env.LE.addAxiom _ infinityAxiom))

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

theorem holEnv_axioms_eta : etaAxiom ∈ holEnv.axioms :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem holEnv_axioms_select : selectAxiom ∈ holEnv.axioms :=
  List.Mem.tail _ (List.Mem.head _)

theorem holEnv_axioms_infinity : infinityAxiom ∈ holEnv.axioms :=
  List.Mem.head _

theorem HOLAxiom.mem_holEnv {p} (h : HOLAxiom p) : p ∈ holEnv.axioms := by
  cases h with
  | eta => exact holEnv_axioms_eta
  | select => exact holEnv_axioms_select
  | infinity => exact holEnv_axioms_infinity

theorem holEnv_WF : holEnv.WF := by
  have hη := holLogic_WF.addAxiom (HasType.of_etaAxiom (env := holLogic))
  have hsel := hη.addAxiom
    ((HasType.of_selectAxiom (env := holLogic)).weakenEnv (Env.LE.addAxiom holLogic etaAxiom))
  exact hsel.addAxiom
    ((HasType.of_infinityAxiom (env := holLogic)).weakenEnv
      ((Env.LE.addAxiom holLogic etaAxiom).trans
        (Env.LE.addAxiom (holLogic.addAxiom etaAxiom) selectAxiom)))

theorem Provable.hol_ax {p} (h : HOLAxiom p) : [] ⊩[holEnv] p :=
  of_axiom holEnv_WF (HOLAxiom.mem_holEnv h)

end HOLean
