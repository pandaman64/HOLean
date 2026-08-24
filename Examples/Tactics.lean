/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Derived
import HOLean.Elab.Decl

/-!
# Backward HOL tactics (examples)

`htheorem … := hby …` scripts rebuild LCF `Thm` values and assemble a
`ProvTrace` into a kernel `Provable` proof (`buildProvable`).  Incomplete
scripts report remaining subgoals at the `hby` block (the cursor after
the last tactic).
-/

namespace Examples.Tactics

open HOLean
open HOLean.Elab
open HOLean.Provable
open Hol

/-! ## Seed theorems via kernel `Provable` proofs -/

private def folX : Name := "_hol_tac_conj_fresh"

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

htheorem and_tt : True ∧ True :=
  prov_and_tt

htheorem and_tt_eq_T : (True ∧ True) = True :=
  prov_and_tt_eq

/-! ## Tactic scripts (`:= hby`) -/

htheorem true_eq_true_tac : True = True := hby
  hrefl

htheorem true_intro_tac : True := hby
  htruth

htheorem and_tt_again : True ∧ True := hby
  hexact and_tt

htheorem true_via_eqmp : True := hby
  happly and_tt_eq_T
  hexact and_tt

htheorem true_eq_true_sym : True = True := hby
  hsym
  hrefl

/-! ## Left binders (Lean-style telescope) -/

hdef constLeft {A : Type} (x : A) (_y : A) := x

htheorem eq_refl {A : Type} (x : A) : x = x := hby
  hrefl

#check true_eq_true_tac_hol_prov
#check true_intro_tac_hol_prov
#check and_tt_again_hol_prov
#check true_via_eqmp_hol_prov
#check true_eq_true_sym_hol_prov
#check eq_refl_hol_prov

#print axioms true_eq_true_tac_hol_prov
#print axioms true_via_eqmp_hol_prov
#print axioms eq_refl_hol_prov

#hol_cert

/-! Hypothesis binders (`DISCH`) are executable but not yet `Provable`-replayed. -/

htheorem true_of_true (_h : True) : True := hby
  hassumption

end Examples.Tactics
