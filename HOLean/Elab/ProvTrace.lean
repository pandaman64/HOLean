/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Syntax.Tm

/-!
# Derivation traces for HOL tactics

A compact description of the LCF steps a tactic script used.
`HOLean.Elab.Replay.buildProvable` turns this into a kernel `Provable`
term; the executable `Thm` checker does not consume it.
-/

namespace HOLean.Elab

/-- Trace of kernel / derived steps producing `hyps ⊢ concl`.

`named` stores the Lean name of the user `htheorem` (without `_hol_prov`);
replay looks up `{leanN}_hol_prov`. -/
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
  /-- `GEN x α`: wrap the conclusion as `∀ x. t`. -/
  | gen (x : HOLean.Name) (α : Ty) (h : ProvTrace)
  /-- `DISCH p`: wrap the conclusion as `p ⇒ q`.  Not yet replayed as
  `Provable`. -/
  | disch (p : Tm) (h : ProvTrace)
  /-- Unsolved subgoal.  Present in an intermediate goal stack; forbidden
  in a closed certificate. -/
  | hole
  deriving Inhabited, Repr

/-- `true` if the trace mentions `ASSUME` (not a closed-theorem certificate). -/
def ProvTrace.usesAssume : ProvTrace → Bool
  | .assume _ => true
  | .eqMp a b => a.usesAssume || b.usesAssume
  | .eqSym h | .instType _ h | .gen _ _ h | .disch _ h => h.usesAssume
  | .refl .. | .truth | .named _ | .hole => false

/-- `true` if this trace discharges a binder hypothesis. -/
def ProvTrace.usesDisch : ProvTrace → Bool
  | .disch _ _ => true
  | .eqMp a b => a.usesDisch || b.usesDisch
  | .eqSym h | .instType _ h | .gen _ _ h => h.usesDisch
  | .assume _ | .refl .. | .truth | .named _ | .hole => false

/-- `true` if any subgoal has not been filled. -/
def ProvTrace.hasHole : ProvTrace → Bool
  | .hole => true
  | .eqMp a b => a.hasHole || b.hasHole
  | .eqSym h | .instType _ h | .gen _ _ h | .disch _ h => h.hasHole
  | .refl .. | .truth | .named _ | .assume _ => false

/-- Number of unsolved subgoals in this (possibly partial) derivation. -/
def ProvTrace.countHoles : ProvTrace → Nat
  | .hole => 1
  | .eqMp a b => a.countHoles + b.countHoles
  | .eqSym h | .instType _ h | .gen _ _ h | .disch _ h => h.countHoles
  | .refl .. | .truth | .named _ | .assume _ => 0

/-- Replace the leftmost `hole` with `new`. -/
def ProvTrace.fillHole (t new : ProvTrace) : Option ProvTrace :=
  match t with
  | .hole => some new
  | .eqMp a b =>
    match fillHole a new with
    | some a' => some (.eqMp a' b)
    | none => (fillHole b new).map (.eqMp a)
  | .eqSym h => (fillHole h new).map eqSym
  | .instType θ h => (fillHole h new).map (instType θ)
  | .gen x α h => (fillHole h new).map (gen x α)
  | .disch p h => (fillHole h new).map (disch p)
  | .refl .. | .truth | .named _ | .assume _ => none

end HOLean.Elab
