/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Elab.Kernel

/-!
# Backward HOL tactics (uncertified)

A small goal-directed front-end over the executable LCF kernel (`Hol.*`).
Tactics rebuild a `Thm` by composing kernel rules; they do **not** yet
emit a kernel `Provable` proof term, so `htheorem … by …` follows the
HolM certificate path (WF / connectives only).

## Tactics

* `h_refl` / `h_rfl` — close `t = t`
* `h_truth` — close `True`
* `h_assumption` — close when the conclusion is among the hypotheses
* `h_sym` — turn `s = t` into `t = s`
* `h_exact n` — close with a named `htheorem` (type-instantiated)
* `h_apply n` — close if possible; otherwise use `EQ_MP` / `SYM` when `n`
  proves an equation matching the goal
* `h_eq_mp n` — require an equation theorem and replace the goal via `EQ_MP`

Atoms are prefixed with `h_` so they do not steal Lean keywords such as
`rfl` / `exact` / `apply`.

## Syntax

```
htheorem foo : True = True by h_refl

htheorem bar : True by h_apply and_tt_eq, h_exact and_tt
```
-/

open Lean

namespace HOLean.Elab

/-- Match schematic type variables in `pat` against `tgt`, extending `acc`. -/
partial def matchTm (pat tgt : Tm) (acc : TySubst := []) : Option TySubst :=
  match pat, tgt with
  | .bvar i, .bvar j =>
    if i == j then some acc else none
  | .fvar x α, .fvar y β =>
    if x == y then α.matchTy β acc else none
  | .const n α, .const m β =>
    if n == m then α.matchTy β acc else none
  | .app f a, .app g b => do
    let acc ← matchTm f g acc
    matchTm a b acc
  | .lam α t, .lam β u => do
    let acc ← α.matchTy β acc
    matchTm t u acc
  | _, _ => none

/-- Instantiate a theorem so its conclusion equals `goal`, if possible. -/
def instantiateToGoal (th : Thm) (goal : Tm) : HolM Thm := do
  if th.concl == goal then
    return th
  match matchTm th.concl goal with
  | some θ =>
    let th ← Hol.instType θ th
    unless th.concl == goal do
      HolM.throw s!"apply: after INST_TYPE, concl {repr th.concl} ≠ goal {repr goal}"
    return th
  | none =>
    HolM.throw s!"apply: cannot match {repr th.concl} to {repr goal}"

/-- Goal-directed proof state. `cont th` lifts a proof of the current
conclusion to a proof of the original statement. -/
structure HolTacState where
  hyps : List Tm
  concl : Tm
  cont : Thm → HolM Thm
  done? : Option Thm := none

abbrev HolTacM := StateT HolTacState HolM

def HolTacM.run (x : HolTacM α) (st : HolTacState) : HolM (α × HolTacState) :=
  StateT.run x st

def HolTacM.throw (msg : String) : HolTacM α :=
  fun _ => .error msg

def getGoal : HolTacM (List Tm × Tm) := do
  let st ← get
  match st.done? with
  | some _ => HolTacM.throw "no goals to be solved"
  | none => return (st.hyps, st.concl)

def closeWith (th : Thm) : HolTacM Unit := do
  let st ← get
  match st.done? with
  | some _ => HolTacM.throw "no goals to be solved"
  | none =>
    unless th.concl == st.concl do
      HolTacM.throw s!"tactic produced {repr th.concl}, expected {repr st.concl}"
    unless th.hyps == st.hyps do
      HolTacM.throw s!"hypothesis mismatch: theorem has {repr th.hyps}, \
        goal has {repr st.hyps}"
    let final ← liftM <| st.cont th
    set { st with done? := some final, concl := th.concl }

def replaceConcl (newConcl : Tm) (step : Thm → HolM Thm) : HolTacM Unit := do
  let st ← get
  match st.done? with
  | some _ => HolTacM.throw "no goals to be solved"
  | none =>
    set {
      st with
      concl := newConcl
      cont := fun th => do
        let th ← step th
        st.cont th
    }

def ensureOpen : HolTacM Unit := do
  let st ← get
  if st.done?.isSome then
    HolTacM.throw "no goals to be solved"

/-- `REFL`: close `t = t`. -/
def tacRefl : HolTacM Unit := do
  ensureOpen
  let (_, concl) ← getGoal
  match Tm.destEq concl with
  | some (_, s, t) =>
    unless s == t do
      HolTacM.throw s!"refl: sides differ\n  {repr s}\n  {repr t}"
    closeWith (← liftM <| Hol.refl s)
  | none => HolTacM.throw s!"refl: expected an equation, got {repr concl}"

/-- Close `True`. -/
def tacTruth : HolTacM Unit := do
  ensureOpen
  let (_, concl) ← getGoal
  unless concl == Tm.tru do
    HolTacM.throw s!"truth: expected True, got {repr concl}"
  closeWith (← liftM <| Hol.truth)

/-- Close when the conclusion is an assumed hypothesis. -/
def tacAssumption : HolTacM Unit := do
  ensureOpen
  let (hyps, concl) ← getGoal
  unless hyps.contains concl do
    HolTacM.throw s!"assumption: {repr concl} is not among the hypotheses"
  unless hyps == [concl] do
    HolTacM.throw "assumption: weakening of hypotheses is not implemented yet"
  closeWith (← liftM <| Hol.assume concl)

/-- Turn goal `s = t` into `t = s`. -/
def tacSym : HolTacM Unit := do
  ensureOpen
  let (_, concl) ← getGoal
  match Tm.destEq concl with
  | some (α, s, t) =>
    replaceConcl (Tm.mkEq α t s) fun th => Hol.sym th
  | none => HolTacM.throw s!"sym: expected an equation, got {repr concl}"

def resolveThm (n : HOLean.Name) : HolTacM Thm :=
  liftM <| Hol.thm n

/-- Close with a named theorem, instantiating type variables if needed. -/
def tacExact (n : HOLean.Name) : HolTacM Unit := do
  ensureOpen
  let (_, concl) ← getGoal
  let th ← resolveThm n
  let th ← liftM <| instantiateToGoal th concl
  closeWith th

/-- Prefer closing; otherwise `EQ_MP` / `SYM` when `n` is an equation. -/
def tacApply (n : HOLean.Name) : HolTacM Unit := do
  ensureOpen
  let (_, concl) ← getGoal
  let th0 ← resolveThm n
  -- Try to close with type instantiation.
  let closed ← liftM do
    try
      let th ← instantiateToGoal th0 concl
      pure (some th)
    catch _ =>
      pure none
  match closed with
  | some th => closeWith th
  | none =>
    match Tm.destEq th0.concl with
    | some (_, p, q) =>
      if q == concl then
        replaceConcl p fun hp => Hol.eqMp th0 hp
      else if p == concl then
        let thSym ← liftM <| Hol.sym th0
        replaceConcl q fun hq => Hol.eqMp thSym hq
      else
        match matchTm q concl, matchTm p concl with
        | some θ, _ =>
          let th ← liftM <| Hol.instType θ th0
          match Tm.destEq th.concl with
          | some (_, p', q') =>
            unless q' == concl do
              HolTacM.throw s!"apply: instantiated RHS {repr q'} ≠ {repr concl}"
            replaceConcl p' fun hp => Hol.eqMp th hp
          | none => HolTacM.throw "apply: expected equation after INST_TYPE"
        | none, some θ =>
          let th ← liftM <| Hol.instType θ th0
          let th ← liftM <| Hol.sym th
          match Tm.destEq th.concl with
          | some (_, p', q') =>
            unless q' == concl do
              HolTacM.throw s!"apply: instantiated RHS {repr q'} ≠ {repr concl}"
            replaceConcl p' fun hp => Hol.eqMp th hp
          | none => HolTacM.throw "apply: expected equation after SYM"
        | none, none =>
          HolTacM.throw s!"apply: theorem {n} does not match goal {repr concl}"
    | none =>
      HolTacM.throw s!"apply: theorem {n} does not match goal {repr concl}"

/-- Require an equation theorem and replace the goal via `EQ_MP`. -/
def tacEqMp (n : HOLean.Name) : HolTacM Unit := do
  ensureOpen
  let (_, concl) ← getGoal
  let th0 ← resolveThm n
  match Tm.destEq th0.concl with
  | some (_, p, q) =>
    if q == concl then
      replaceConcl p fun hp => Hol.eqMp th0 hp
    else if p == concl then
      let thSym ← liftM <| Hol.sym th0
      replaceConcl q fun hq => Hol.eqMp thSym hq
    else
      HolTacM.throw s!"eq_mp: neither side of {repr th0.concl} is the goal {repr concl}"
  | none => HolTacM.throw s!"eq_mp: expected an equation theorem, got {repr th0.concl}"

/-- Run a tactic script against a closed goal `⊢ stmt`. -/
def runHolTactics (stmt : Tm) (script : HolTacM Unit) : HolM Thm := do
  let st : HolTacState := {
    hyps := []
    concl := stmt
    cont := pure
  }
  let (_, st) ← HolTacM.run script st
  match st.done? with
  | some th =>
    unless th.hyps.isEmpty do
      HolM.throw s!"unsolved hypotheses: {repr th.hyps}"
    unless th.concl == stmt do
      HolM.throw s!"proved {repr th.concl}, expected {repr stmt}"
    return th
  | none =>
    HolM.throw s!"unsolved goal: {repr st.concl}"

/-! ## Syntax -/

declare_syntax_cat hol_tac

syntax "h_refl" : hol_tac
syntax "h_rfl" : hol_tac
syntax "h_truth" : hol_tac
syntax "h_assumption" : hol_tac
syntax "h_sym" : hol_tac
syntax "h_exact " ident : hol_tac
syntax "h_apply " ident : hol_tac
syntax "h_eq_mp " ident : hol_tac

/-- Parse a tactic name from an identifier (uses the short HOL name). -/
def holTacName (id : TSyntax `ident) : HOLean.Name :=
  holName id.getId

def elabHolTac (stx : Syntax) : HolTacM Unit := do
  match stx with
  | `(hol_tac| h_refl) | `(hol_tac| h_rfl) => tacRefl
  | `(hol_tac| h_truth) => tacTruth
  | `(hol_tac| h_assumption) => tacAssumption
  | `(hol_tac| h_sym) => tacSym
  | `(hol_tac| h_exact $n:ident) => tacExact (holTacName n)
  | `(hol_tac| h_apply $n:ident) => tacApply (holTacName n)
  | `(hol_tac| h_eq_mp $n:ident) => tacEqMp (holTacName n)
  | _ => HolTacM.throw s!"unsupported HOL tactic: {stx}"

def elabHolTacSeq (stxs : Array Syntax) : HolTacM Unit :=
  stxs.forM elabHolTac

/-- Evaluate a `by …` tactic script for `⊢ stmt`. -/
def evalHolTacProof (stmt : Tm) (tacs : Array Syntax) (ctx : HolCtx) : Except String Thm :=
  HolM.run (runHolTactics stmt (elabHolTacSeq tacs)) ctx

end HOLean.Elab
