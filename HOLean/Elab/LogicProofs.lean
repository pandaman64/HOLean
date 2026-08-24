/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Derived
import HOLean.Elab.Decl

/-!
# `and` / `or` facts via `htheorem`

Basic connective facts are proved in the kernel (`Provable`) and installed
with `htheorem` by giving a `[] ⊩[holEnv] …` proof.  Use parentheses in
statements: `∧` binds tighter than `=`, so write `(True ∧ True) = True`.
-/

namespace HOLean.Elab.LogicProofs

open HOLean
open HOLean.Elab
open HOLean.Provable
open Hol

private def folX : Name := "_hol_conj_fresh"

private theorem folX_tru_not_free :
    Tm.tru.freeIn folX Tm.boolCombTy = false ∧
      Tm.tru.freeIn folX .bool = false := by
  simp [folX, Tm.tru_not_free, Tm.boolCombTy]

theorem prov_and_tt : [] ⊩[holEnv] Tm.and Tm.tru Tm.tru :=
  conj folX tru_intro tru_intro
    (by simp [Tm.tru])
    (by simp [Tm.tru])
    (by intro r hr; cases hr)
    (by intro r hr; cases hr)
    (by exact folX_tru_not_free.1)
    (by exact folX_tru_not_free.1)
    folX_tru_not_free.2

theorem prov_and_tt_eq : [] ⊩[holEnv] Tm.mkEq .bool (Tm.and Tm.tru Tm.tru) Tm.tru := by
  have h := prov_and_tt
  exact eqt_intro h (by simp [Tm.tru])

theorem prov_and_tt_left : [] ⊩[holEnv] Tm.tru :=
  and_elim_left folX prov_and_tt
    HasType.tru HasType.tru
    (by exact folX_tru_not_free.1)
    (by exact folX_tru_not_free.1)
    folX_tru_not_free.2

/-! Installed theorems -/

htheorem and_tt_conj : True ∧ True :=
  prov_and_tt

htheorem and_tt_eq : (True ∧ True) = True :=
  prov_and_tt_eq

htheorem and_tt_left : True :=
  prov_and_tt_left

htheorem and_tt_left_again : and_tt_left :=
  Hol.thm "and_tt_left"

/-! De Morgan (e.g. `¬(p ∧ q) = (¬p) ∨ (¬q)`) is not yet in `Derived`; concrete
instances also do not follow from kernel `refl` alone because `∧`/`∨`/`¬` unfold
to combinator definitions rather than truth-table values. -/

end HOLean.Elab.LogicProofs
