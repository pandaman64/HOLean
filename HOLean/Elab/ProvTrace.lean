/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Syntax.Tm

/-!
# Derivation traces for HOL tactics

A compact description of the LCF steps a tactic script used.  Replay
backends (proof-producing `Provable` terms vs Lean `apply`) consume this;
the executable `Thm` checker does not.
-/

namespace HOLean.Elab

/-- Trace of kernel / derived steps producing `hyps ⊢ concl`.

`named` stores the Lean name of the user `htheorem` (without `_hol_prov`);
replay resolves B vs C certificates from that. -/
inductive ProvTrace where
  /-- `REFL t` at type `α`. -/
  | refl (t : Tm) (α : Ty)
  /-- `⊢ T` via `Provable.tru_intro`. -/
  | truth
  /-- Previously installed `htheorem` (Lean name). -/
  | named (leanN : Lean.Name)
  /-- `EQ_MP`. -/
  | eqMp (hEq hP : ProvTrace)
  /-- Derived `eq_sym`. -/
  | eqSym (h : ProvTrace)
  /-- `INST_TYPE θ`. -/
  | instType (θ : TySubst) (h : ProvTrace)
  /-- `ASSUME p`.  Closed `htheorem` scripts never replay this. -/
  | assume (p : Tm)
  deriving Inhabited, Repr

/-- `true` if the trace mentions `ASSUME` (not a closed-theorem certificate). -/
def ProvTrace.usesAssume : ProvTrace → Bool
  | .assume _ => true
  | .eqMp a b => a.usesAssume || b.usesAssume
  | .eqSym h | .instType _ h => h.usesAssume
  | .refl .. | .truth | .named _ => false

end HOLean.Elab
