/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Syntax.Tm

/-!
# Derivation traces for HOL tactics

A compact description of the LCF steps a forward script or tactic used.
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
  /-- `TRANS`. -/
  | trans (h1 h2 : ProvTrace)
  /-- `MK_COMB`. -/
  | mkComb (h1 h2 : ProvTrace)
  /-- `ABS`: close free variable `(x, α)`. -/
  | abs (x : HOLean.Name) (α : Ty) (h : ProvTrace)
  /-- `BETA`: `((λ x. t) x) = t[x]`. -/
  | beta (t : Tm) (x : HOLean.Name) (α : Ty)
  /-- `ASSUME p`.  Closed `htheorem` scripts never replay this. -/
  | assume (p : Tm)
  /-- `EQ_MP`. -/
  | eqMp (hEq hP : ProvTrace)
  /-- `DEDUCT_ANTISYM`. -/
  | deductAntisym (h1 h2 : ProvTrace)
  /-- `INST_TYPE θ`. -/
  | instType (θ : TySubst) (h : ProvTrace)
  /-- `INST σ`. -/
  | inst (σ : Tm.Subst) (h : ProvTrace)
  /-- Environment axiom / definitional equation `⊢ p`. -/
  | ax (p : Tm)
  /-- `⊢ T` via `Provable.tru_intro`. -/
  | truth
  /-- Previously installed `htheorem` (Lean name). -/
  | named (leanN : Lean.Name)
  /-- Derived `eq_sym`. -/
  | eqSym (h : ProvTrace)
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
  | .trans a b | .mkComb a b | .eqMp a b | .deductAntisym a b =>
    a.usesAssume || b.usesAssume
  | .abs _ _ h | .instType _ h | .inst _ h | .eqSym h | .gen _ _ h | .disch _ h =>
    h.usesAssume
  | .refl .. | .beta .. | .ax _ | .truth | .named _ | .hole => false

/-- `true` if this trace discharges a binder hypothesis. -/
def ProvTrace.usesDisch : ProvTrace → Bool
  | .disch _ _ => true
  | .trans a b | .mkComb a b | .eqMp a b | .deductAntisym a b =>
    a.usesDisch || b.usesDisch
  | .abs _ _ h | .instType _ h | .inst _ h | .eqSym h | .gen _ _ h =>
    h.usesDisch
  | .assume _ | .refl .. | .beta .. | .ax _ | .truth | .named _ | .hole => false

/-- `true` if any subgoal has not been filled. -/
def ProvTrace.hasHole : ProvTrace → Bool
  | .hole => true
  | .trans a b | .mkComb a b | .eqMp a b | .deductAntisym a b =>
    a.hasHole || b.hasHole
  | .abs _ _ h | .instType _ h | .inst _ h | .eqSym h | .gen _ _ h | .disch _ h =>
    h.hasHole
  | .refl .. | .beta .. | .assume _ | .ax _ | .truth | .named _ => false

/-- Number of unsolved subgoals in this (possibly partial) derivation. -/
def ProvTrace.countHoles : ProvTrace → Nat
  | .hole => 1
  | .trans a b | .mkComb a b | .eqMp a b | .deductAntisym a b =>
    a.countHoles + b.countHoles
  | .abs _ _ h | .instType _ h | .inst _ h | .eqSym h | .gen _ _ h | .disch _ h =>
    h.countHoles
  | .refl .. | .beta .. | .assume _ | .ax _ | .truth | .named _ => 0

/-- Replace the leftmost `hole` with `new`. -/
def ProvTrace.fillHole (t new : ProvTrace) : Option ProvTrace :=
  match t with
  | .hole => some new
  | .trans a b =>
    match fillHole a new with
    | some a' => some (.trans a' b)
    | none => (fillHole b new).map (.trans a)
  | .mkComb a b =>
    match fillHole a new with
    | some a' => some (.mkComb a' b)
    | none => (fillHole b new).map (.mkComb a)
  | .eqMp a b =>
    match fillHole a new with
    | some a' => some (.eqMp a' b)
    | none => (fillHole b new).map (.eqMp a)
  | .deductAntisym a b =>
    match fillHole a new with
    | some a' => some (.deductAntisym a' b)
    | none => (fillHole b new).map (.deductAntisym a)
  | .abs x α h => (fillHole h new).map (abs x α)
  | .instType θ h => (fillHole h new).map (instType θ)
  | .inst σ h => (fillHole h new).map (inst σ)
  | .eqSym h => (fillHole h new).map eqSym
  | .gen x α h => (fillHole h new).map (gen x α)
  | .disch p h => (fillHole h new).map (disch p)
  | .refl .. | .beta .. | .assume _ | .ax _ | .truth | .named _ => none

end HOLean.Elab
