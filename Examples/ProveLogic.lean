/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Elab.ProveDecl

/-!
# Connective intro/elim in `ProveM`

Each theorem is an LCF script: kernel primitives plus the `Hol.*` helpers
in `Prove/Conv.lean` and `Prove/Logic.lean`.  No `Provable.*` metatheorems
from `HOLean.Derived` are used.
-/

namespace Examples.ProveLogic

open HOLean
open HOLean.Prove
open Hol

/-! ## `True` -/

htheorem' true_intro : True :=
  Hol.truth

htheorem' and_tt : True ∧ True := do
  Hol.conj (← Hol.truth) (← Hol.truth)

htheorem' eqt_elim_true (p : Prop) (h : p = True) : p := do
  Hol.eqtElim (← Hol.assume (hol_tm(p = True)))

/-! ## `∧` -/

htheorem' and_intro (p q : Prop) (hp : p) (hq : q) : p ∧ q := do
  Hol.conj (← Hol.assume (hol_tm(p))) (← Hol.assume (hol_tm(q)))

htheorem' and_elim1 (p q : Prop) (h : p ∧ q) : p := do
  Hol.conjunct1 (← Hol.assume (hol_tm(p ∧ q)))

htheorem' and_elim2 (p q : Prop) (h : p ∧ q) : q := do
  Hol.conjunct2 (← Hol.assume (hol_tm(p ∧ q)))

/-! ## `→` -/

htheorem' imp_intro (p q : Prop) (hq : q) : p → q := do
  Hol.disch (hol_tm(p)) (← Hol.assume (hol_tm(q)))

htheorem' imp_elim (p q : Prop) (him : p → q) (hp : p) : q := do
  Hol.mp (← Hol.assume (hol_tm(p → q))) (← Hol.assume (hol_tm(p)))

/-! ## `∀` -/

htheorem' forall_intro {A : Type} (x : A) : x = x :=
  Hol.refl (hol_tm(x))

htheorem' forall_elim {A : Type} (P : A → Prop) (x : A) (h : ∀ y : A, P y) : P x := do
  Hol.spec (hol_tm(x)) (← Hol.assume (hol_tm(∀ y : A, P y)))

/-! ## `False` / `¬` -/

htheorem' false_elim (p : Prop) (h : False) : p := do
  Hol.falsumElim (hol_tm(p)) (← Hol.assume (hol_tm(False)))

htheorem' not_intro (p : Prop) (h : p → False) : ¬ p := do
  Hol.notIntro (← Hol.assume (hol_tm(p → False)))

htheorem' not_elim (p : Prop) (hn : ¬ p) (hp : p) : False := do
  Hol.mp (← Hol.notElim (← Hol.assume (hol_tm(¬ p)))) (← Hol.assume (hol_tm(p)))

/-! ## `∨` -/

htheorem' or_intro1 (p q : Prop) (hp : p) : p ∨ q := do
  Hol.disj1 (hol_tm(q)) (← Hol.assume (hol_tm(p)))

htheorem' or_intro2 (p q : Prop) (hq : q) : p ∨ q := do
  Hol.disj2 (hol_tm(p)) (← Hol.assume (hol_tm(q)))

htheorem' or_elim (p q r : Prop) (h : p ∨ q) (hp : p → r) (hq : q → r) : r := do
  Hol.disjElim
    (← Hol.assume (hol_tm(p ∨ q)))
    (← Hol.assume (hol_tm(p → r)))
    (← Hol.assume (hol_tm(q → r)))

/-! ## `∃` -/

htheorem' exists_intro {A : Type} (P : A → Prop) (x : A) (h : P x) : ∃ y, P y := do
  Hol.existsIntro (hol_tm(∃ y, P y)) (hol_tm(x)) (← Hol.assume (hol_tm(P x)))

htheorem' exists_elim {A : Type} (P : A → Prop) (q : Prop)
    (hex : ∃ y, P y) (h : ∀ y : A, P y → q) : q := do
  Hol.existsElim (hol_tm(q))
    (← Hol.assume (hol_tm(∃ y, P y)))
    (← Hol.assume (hol_tm(∀ y : A, P y → q)))

#check true_intro_hol_prov
#check and_intro_hol_prov
#check and_elim1_hol_prov
#check imp_elim_hol_prov
#check forall_elim_hol_prov
#check false_elim_hol_prov
#check not_intro_hol_prov
#check or_intro1_hol_prov
#check or_elim_hol_prov
#check exists_intro_hol_prov
#check exists_elim_hol_prov

#print axioms and_intro_hol_prov
#print axioms or_elim_hol_prov
#print axioms exists_elim_hol_prov

#hol_cert

end Examples.ProveLogic
