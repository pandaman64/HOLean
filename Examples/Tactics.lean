/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Derived
import HOLean.Elab.Decl

/-!
# Backward HOL tactics (examples)

Uncertified `htheorem … by …` scripts rebuild LCF `Thm` values from the
kernel combinators. Consistency certificates are not emitted for this
path yet; see `HOLean.Elab.Tactic`.
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

/-! ## Tactic scripts -/

htheorem true_eq_true_tac : True = True by hrefl

htheorem true_intro_tac : True by htruth

htheorem and_tt_again : True ∧ True by hexact and_tt

htheorem true_via_eqmp : True by happly and_tt_eq_T, hexact and_tt

htheorem true_eq_true_sym : True = True by hsym, hrefl

end Examples.Tactics
