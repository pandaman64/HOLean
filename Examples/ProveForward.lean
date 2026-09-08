/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Elab.ProveDecl

/-!
# Forward LCF scripts (`htheorem'`)

Verified `ProveM` scripts.  Closed theorems emit `{name}_hol_prov` via
`extractProvable`, not `ProvTrace` replay.
-/

namespace Examples.ProveForward

open HOLean
open HOLean.Prove
open Hol

htheorem' true_eq_true_fwd : True = True :=
  Hol.refl (hol_tm(True))

htheorem' true_eq_true_trans : True = True := do
  let th ← Hol.refl (hol_tm(True))
  Hol.trans th (← Hol.refl (hol_tm(True)))

htheorem' true_intro_fwd : True :=
  Hol.truth

htheorem' true_eq_true_sym_fwd : True = True := do
  Hol.sym (← Hol.refl (hol_tm(True)))

htheorem' tru_defn_eq : True = ((fun (p : Prop) => p) = (fun (p : Prop) => p)) :=
  Hol.defn "tru"

htheorem' true_via_eqmp_fwd : True := do
  let heq ← Hol.sym (← Hol.defn "tru")
  let hr ← Hol.refl (hol_tm(fun (p : Prop) => p))
  Hol.eqMp heq hr

htheorem' true_eq_true_again : True = True :=
  Hol.thm "true_eq_true_fwd"

#check true_eq_true_fwd_hol_prov
#check true_eq_true_trans_hol_prov
#check true_intro_fwd_hol_prov
#check true_eq_true_sym_fwd_hol_prov
#check tru_defn_eq_hol_prov
#check true_via_eqmp_fwd_hol_prov
#check true_eq_true_again_hol_prov

#print axioms true_eq_true_fwd_hol_prov
#print axioms true_via_eqmp_fwd_hol_prov
#print axioms tru_defn_eq_hol_prov

#hol_cert

end Examples.ProveForward
