/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean.Elab.Command
import HOLean.Elab.Kernel
import HOLean.Elab.ProvTrace

/-!
# Backward HOL tactics

A HOL Light / Candle-style goal stack: remaining sequents plus a
`ProvTrace` with `hole`s (left-to-right) that record how to reassemble
an LCF theorem once those subgoals are solved.

Tactics act on the *current* (first) goal.  `htheorem … := hby …`
requires the stack to be empty; `hbegin` / `htac` / `#hol_goals` /
`hend` expose the same state across commands.

Closed traces are assembled into `Provable` by `HOLean.Elab.Replay.buildProvable`.

## Tactics

* `hrefl` / `hrfl` — close `t = t`
* `htruth` — close `True`
* `hassumption` — close when the conclusion is among the hypotheses
  (not certified: `ASSUME` leaves a hypothesis)
* `hsym` — turn `s = t` into `t = s`
* `hexact n` — close with a named `htheorem` (type-instantiated)
* `happly n` — close if possible; otherwise use `EQ_MP` / `SYM` when `n`
  proves an equation matching the goal
* `heqmp n` — require an equation theorem and replace the goal via `EQ_MP`
* `_` — proof hole: report the current sequents (InfoView MVP)

## Syntax

```
hdef foobar {A : Type} (x : A) := x

htheorem foo : True = True := hby
  hrefl

htheorem bar : True := hby
  happly and_tt_eq
  hexact and_tt

htheorem eq_refl {A : Type} (x : A) : x = x := hby
  hrefl

hbegin baz : True
htac happly and_tt_eq
#hol_goals
htac hexact and_tt
hend
```
-/

open Lean Elab Command

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

/-- A checked sequent plus the derivation used to obtain it. -/
structure CertifiedThm where
  thm : Thm
  trace : ProvTrace
  deriving Inhabited

/-- One open HOL sequent. -/
structure HolGoal where
  hyps : List Tm
  concl : Tm
  deriving Inhabited, Repr, BEq

def formatGoalString (g : HolGoal) : String :=
  match g.hyps with
  | [] => s!"⊢ {repr g.concl}"
  | hyps =>
    let hs := String.intercalate ", " (hyps.map fun p => s!"{repr p}")
    s!"{hs} ⊢ {repr g.concl}"

def formatGoalsString (gs : List HolGoal) : String :=
  match gs with
  | [] => "No subgoals"
  | gs =>
    let n := gs.length
    Id.run do
      let mut s := s!"{n} subgoal(s)"
      let mut i := 1
      for g in gs do
        s := s ++ s!"\n[{i}/{n}] {formatGoalString g}"
        i := i + 1
      return s

/-- Goal stack in the HOL Light style: remaining goals plus a (possibly
partial) derivation whose holes, left to right, match `goals`. -/
structure HolTacState where
  stmt : Tm
  goals : List HolGoal
  frame : ProvTrace
  deriving Inhabited

def wrapClosedFrame (hyps : List Tm) (params : List (HOLean.Name × Ty))
    (inner : ProvTrace) : ProvTrace :=
  params.foldr (fun (n, α) t => ProvTrace.gen n α t)
    (hyps.foldr (fun p t => ProvTrace.disch p t) inner)

def HolTacState.initGoal (stmt : Tm) (hyps : List Tm) (concl : Tm)
    (params : List (HOLean.Name × Ty) := []) : HolTacState :=
  { stmt
    goals := [{ hyps, concl }]
    frame := wrapClosedFrame hyps params .hole }

def HolTacState.init (stmt : Tm) : HolTacState :=
  HolTacState.initGoal stmt [] stmt

abbrev HolTacM := StateT HolTacState HolM

def HolTacM.run (x : HolTacM α) (st : HolTacState) : HolM (α × HolTacState) :=
  StateT.run x st

def HolTacM.throw (msg : String) : HolTacM α :=
  fun _ => .error msg

def ensureOpen : HolTacM Unit := do
  let st ← get
  if st.goals.isEmpty then
    HolTacM.throw "no goals to be solved"

def getGoal : HolTacM HolGoal := do
  ensureOpen
  let st ← get
  match st.goals with
  | g :: _ => return g
  | [] => HolTacM.throw "no goals to be solved"

/-- Replace the current goal with `news`, plugging `filled` (whose holes
equal `news.length`) into the leftmost hole of the frame. -/
def applyStep (news : List HolGoal) (filled : ProvTrace) : HolTacM Unit := do
  let st ← get
  match st.goals with
  | [] => HolTacM.throw "no goals to be solved"
  | _ :: rest =>
    unless filled.countHoles == news.length do
      HolTacM.throw s!"internal: step has {filled.countHoles} holes, \
        but {news.length} new goal(s)"
    let some frame := st.frame.fillHole filled
      | HolTacM.throw "internal: no hole in the derivation frame"
    unless frame.countHoles == rest.length + news.length do
      HolTacM.throw "internal: hole/goal mismatch after tactic"
    set { st with goals := news ++ rest, frame }

def closeWith (ct : CertifiedThm) : HolTacM Unit := do
  let g ← getGoal
  unless ct.thm.concl == g.concl do
    HolTacM.throw s!"tactic produced {repr ct.thm.concl}, expected {repr g.concl}"
  unless ct.thm.hyps.all g.hyps.contains do
    HolTacM.throw s!"hypothesis mismatch: theorem has {repr ct.thm.hyps}, \
      goal has {repr g.hyps}"
  applyStep [] ct.trace

/-- Refine the current goal to a single new conclusion. `wrap hole` is
the derivation fragment for this step. -/
def replaceConcl (newConcl : Tm) (wrap : ProvTrace → ProvTrace) : HolTacM Unit := do
  let g ← getGoal
  applyStep [{ g with concl := newConcl }] (wrap .hole)

/-- Replay a closed trace through the executable LCF kernel. -/
partial def evalTrace : ProvTrace → HolM Thm
  | .refl t _ => Hol.refl t
  | .truth => Hol.truth
  | .named leanN =>
    let n :=
      match leanN with
      | .str _ s => s
      | _ => leanN.toString
    Hol.thm n
  | .eqMp hEq hP => do
    Hol.eqMp (← evalTrace hEq) (← evalTrace hP)
  | .eqSym h => do
    Hol.sym (← evalTrace h)
  | .instType θ h => do
    Hol.instType θ (← evalTrace h)
  | .assume p => Hol.assume p
  | .gen x α h => do
    Hol.gen x α (← evalTrace h)
  | .disch p h => do
    Hol.disch p (← evalTrace h)
  | .hole => HolM.throw "unsolved HOL goal"

def finishTacState (st : HolTacState) : HolM CertifiedThm := do
  match st.goals with
  | _ :: _ =>
    HolM.throw s!"unsolved HOL goals:\n{formatGoalsString st.goals}"
  | [] =>
    if st.frame.hasHole then
      HolM.throw "internal: derivation still has holes after the goal stack emptied"
    let thm ← evalTrace st.frame
    unless thm.hyps.isEmpty do
      HolM.throw s!"unsolved hypotheses: {repr thm.hyps}"
    unless thm.concl == st.stmt do
      HolM.throw s!"proved {repr thm.concl}, expected {repr st.stmt}"
    return { thm, trace := st.frame }

/-- `REFL`: close `t = t`. -/
def tacRefl : HolTacM Unit := do
  let g ← getGoal
  match Tm.destEq g.concl with
  | some (α, s, t) =>
    unless s == t do
      HolTacM.throw s!"refl: sides differ\n  {repr s}\n  {repr t}"
    closeWith { thm := ← liftM <| Hol.refl s, trace := .refl s α }
  | none => HolTacM.throw s!"refl: expected an equation, got {repr g.concl}"

/-- Close `True`. -/
def tacTruth : HolTacM Unit := do
  let g ← getGoal
  unless g.concl == Tm.tru do
    HolTacM.throw s!"truth: expected True, got {repr g.concl}"
  closeWith { thm := ← liftM <| Hol.truth, trace := .truth }

/-- Close when the conclusion is an assumed hypothesis. -/
def tacAssumption : HolTacM Unit := do
  let g ← getGoal
  unless g.hyps.contains g.concl do
    HolTacM.throw s!"assumption: {repr g.concl} is not among the hypotheses"
  unless g.hyps == [g.concl] do
    HolTacM.throw "assumption: weakening of hypotheses is not implemented yet"
  closeWith { thm := ← liftM <| Hol.assume g.concl, trace := .assume g.concl }

/-- Turn goal `s = t` into `t = s`. -/
def tacSym : HolTacM Unit := do
  let g ← getGoal
  match Tm.destEq g.concl with
  | some (α, s, t) =>
    replaceConcl (Tm.mkEq α t s) ProvTrace.eqSym
  | none => HolTacM.throw s!"sym: expected an equation, got {repr g.concl}"

/-- Look up a user theorem and its Lean `htheorem` name (for `_hol_prov`). -/
def resolveNamed (n : HOLean.Name) : HolTacM (Thm × Lean.Name) := do
  let decls := (← readThe HolCtx).decls
  let th ← liftM <| Hol.thm n
  let some leanN := decls.findSome? fun
      | .thm ln hn _ => if hn == n || ln.toString == n then some ln else none
      | .defn .. => none
    | HolTacM.throw s!"no theorem `{n}`"
  return (th, leanN)

def instantiateCertified (ct : CertifiedThm) (goal : Tm) : HolM CertifiedThm := do
  if ct.thm.concl == goal then
    return ct
  match matchTm ct.thm.concl goal with
  | some θ =>
    let th ← Hol.instType θ ct.thm
    unless th.concl == goal do
      HolM.throw s!"apply: after INST_TYPE, concl {repr th.concl} ≠ goal {repr goal}"
    return { thm := th, trace := .instType θ ct.trace }
  | none =>
    HolM.throw s!"apply: cannot match {repr ct.thm.concl} to {repr goal}"

/-- Close with a named theorem, instantiating type variables if needed. -/
def tacExact (n : HOLean.Name) : HolTacM Unit := do
  let g ← getGoal
  let (th, provN) ← resolveNamed n
  let ct ← liftM <| instantiateCertified { thm := th, trace := .named provN } g.concl
  closeWith ct

def eqMpFragment (leanN : Lean.Name) (useSym : Bool) (θ? : Option TySubst) :
    ProvTrace → ProvTrace := fun hp =>
  let eqTr : ProvTrace :=
    match θ? with
    | some θ => .instType θ (.named leanN)
    | none => .named leanN
  let eqTr := if useSym then .eqSym eqTr else eqTr
  .eqMp eqTr hp

/-- Prefer closing; otherwise `EQ_MP` / `SYM` when `n` is an equation. -/
def tacApply (n : HOLean.Name) : HolTacM Unit := do
  let g ← getGoal
  let (th0, provN) ← resolveNamed n
  let closed ← liftM do
    try
      let ct ← instantiateCertified { thm := th0, trace := .named provN } g.concl
      pure (some ct)
    catch _ =>
      pure none
  match closed with
  | some ct => closeWith ct
  | none =>
    match Tm.destEq th0.concl with
    | some (_, p, q) =>
      if q == g.concl then
        replaceConcl p (eqMpFragment provN false none)
      else if p == g.concl then
        replaceConcl q (eqMpFragment provN true none)
      else
        match matchTm q g.concl, matchTm p g.concl with
        | some θ, _ =>
          let th ← liftM <| Hol.instType θ th0
          match Tm.destEq th.concl with
          | some (_, p', q') =>
            unless q' == g.concl do
              HolTacM.throw s!"apply: instantiated RHS {repr q'} ≠ {repr g.concl}"
            replaceConcl p' (eqMpFragment provN false (some θ))
          | none => HolTacM.throw "apply: expected equation after INST_TYPE"
        | none, some θ =>
          let th ← liftM <| Hol.instType θ th0
          let th ← liftM <| Hol.sym th
          match Tm.destEq th.concl with
          | some (_, p', q') =>
            unless q' == g.concl do
              HolTacM.throw s!"apply: instantiated RHS {repr q'} ≠ {repr g.concl}"
            replaceConcl p' (eqMpFragment provN true (some θ))
          | none => HolTacM.throw "apply: expected equation after SYM"
        | none, none =>
          HolTacM.throw s!"apply: theorem {n} does not match goal {repr g.concl}"
    | none =>
      HolTacM.throw s!"apply: theorem {n} does not match goal {repr g.concl}"

/-- Require an equation theorem and replace the goal via `EQ_MP`. -/
def tacEqMp (n : HOLean.Name) : HolTacM Unit := do
  let g ← getGoal
  let (th0, provN) ← resolveNamed n
  match Tm.destEq th0.concl with
  | some (_, p, q) =>
    if q == g.concl then
      replaceConcl p (eqMpFragment provN false none)
    else if p == g.concl then
      replaceConcl q (eqMpFragment provN true none)
    else
      HolTacM.throw s!"eq_mp: neither side of {repr th0.concl} is the goal {repr g.concl}"
  | none => HolTacM.throw s!"eq_mp: expected an equation theorem, got {repr th0.concl}"

/-- Apply a tactic script to an existing goal stack. -/
def execHolTactics (st : HolTacState) (script : HolTacM Unit) : HolM HolTacState := do
  let (_, st) ← HolTacM.run script st
  return st

/-- Run a tactic script against a closed goal `⊢ stmt` and demand no subgoals. -/
def runHolTactics (stmt : Tm) (script : HolTacM Unit) : HolM CertifiedThm := do
  let st ← execHolTactics (HolTacState.init stmt) script
  finishTacState st

/-! ## Syntax -/

declare_syntax_cat hol_tac

syntax "hrefl" : hol_tac
syntax "hrfl" : hol_tac
syntax "htruth" : hol_tac
syntax "hassumption" : hol_tac
syntax "hsym" : hol_tac
syntax "hexact " ident : hol_tac
syntax "happly " ident : hol_tac
syntax "heqmp " ident : hol_tac
syntax (name := holTacHole) "_" : hol_tac

/-- Indented / semicolon-separated tactic sequence (Lean `by` style). -/
syntax holTacSeq := sepBy1IndentSemicolon(hol_tac)

/-- Parse a tactic name from an identifier (uses the short HOL name). -/
def holTacName (id : TSyntax `ident) : HOLean.Name :=
  holName id.getId

/-- `sepBy1IndentSemicolon` elements of a `holTacSeq`. -/
def holTacsOfSeq (stx : Syntax) : Array Syntax :=
  let args :=
    if stx.getNumArgs > 0 && stx[0].getKind == `null then
      stx[0].getArgs
    else
      stx.getArgs
  Id.run do
    let mut out := #[]
    for arg in args, i in [0:args.size] do
      if i % 2 == 0 && !arg.isMissing then
        out := out.push arg
    return out

def isHolHole : Syntax → Bool
  | `(hol_tac| _) => true
  | _ => false

def elabHolTac (stx : Syntax) : HolTacM Unit := do
  match stx with
  | `(hol_tac| hrefl) | `(hol_tac| hrfl) => tacRefl
  | `(hol_tac| htruth) => tacTruth
  | `(hol_tac| hassumption) => tacAssumption
  | `(hol_tac| hsym) => tacSym
  | `(hol_tac| hexact $n:ident) => tacExact (holTacName n)
  | `(hol_tac| happly $n:ident) => tacApply (holTacName n)
  | `(hol_tac| heqmp $n:ident) => tacEqMp (holTacName n)
  | `(hol_tac| _) =>
    HolTacM.throw s!"unsolved HOL goals:\n{formatGoalsString (← get).goals}"
  | _ => HolTacM.throw s!"unsupported HOL tactic: {stx}"

def elabHolTacSeq (stxs : Array Syntax) : HolTacM Unit :=
  stxs.forM elabHolTac

/-- Evaluate a `hby` tactic script for `⊢ stmt` and demand no subgoals. -/
def evalHolTacProof (stmt : Tm) (tacs : Array Syntax) (ctx : HolCtx) :
    Except String CertifiedThm :=
  HolM.run (runHolTactics stmt (elabHolTacSeq tacs)) ctx

/-- Apply tactics to an existing stack (does not require the proof to be finished). -/
def evalHolTacs (st : HolTacState) (tacs : Array Syntax) (ctx : HolCtx) :
    Except String HolTacState :=
  HolM.run (execHolTactics st (elabHolTacSeq tacs)) ctx

/-- Run tactics one at a time, logging the incoming sequent at each syntax
node so the InfoView can show the intermediate state (MVP). `_` stops and
reports the current goals. -/
def applyHolTacsLocated (st : HolTacState) (tacs : Array Syntax) (ctx : HolCtx) :
    CommandElabM HolTacState := do
  let mut st := st
  for tac in tacs do
    logInfoAt tac m!"{formatGoalsString st.goals}"
    if isHolHole tac then
      throwErrorAt tac m!"HOLean: unsolved goals\n{formatGoalsString st.goals}"
    match evalHolTacs st #[tac] ctx with
    | .error msg =>
      throwErrorAt tac m!"HOLean: {msg}\n{formatGoalsString st.goals}"
    | .ok st' =>
      st := st'
  if st.goals.isEmpty then
    if let some last := tacs.back? then
      logInfoAt last m!"{formatGoalsString st.goals}"
  return st

/-! ## Interactive session (Candle-style `g` / `e`) -/

/-- In-progress `hbegin` proof.  Not persisted to `.olean`. -/
structure HolSession where
  leanN : Lean.Name
  holN : HOLean.Name
  propType : Lean.Expr
  tac : HolTacState

initialize holSessionExt : EnvExtension (Option HolSession) ←
  registerEnvExtension (pure none)

def getHolSession [Monad m] [MonadEnv m] : m (Option HolSession) := do
  return holSessionExt.getState (← getEnv)

def setHolSession [Monad m] [MonadEnv m] (s : Option HolSession) : m Unit :=
  modifyEnv (holSessionExt.setState · s)

end HOLean.Elab
