/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Elab.Term
import HOLean.Elab.Decl

/-!
`#hol t` prints the HOL translation and infers in the current HOL
environment (`holEnv` plus `hdef` / `htheorem`).  `Connective` must not
import this file.
-/

open Lean Meta Elab

namespace HOLean.Elab

def inferHol (t : Tm) : MetaM (Option Ty) := do
  return t.infer (← currentHolEnv) []

def holCommand (stx : Syntax) : TermElabM MessageData := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isProp then
    let t ← exprToTmVal e
    return m!"HOL proposition:{indentD (repr t)}\n\
      infer: {repr (← inferHol t)}"
  else if type.isSort then
    let ty ← exprToTyVal e
    return m!"HOL type:{indentD (repr ty)}"
  else
    let t ← exprToTmVal e
    return m!"HOL term:{indentD (repr t)}\n\
      infer: {repr (← inferHol t)}"

end HOLean.Elab

/-- Print the HOL translation of a Lean4-like term, type, or proposition. -/
elab "#hol " t:term : command => do
  let msg ← Lean.Elab.Command.liftTermElabM (HOLean.Elab.holCommand t)
  Lean.logInfo msg
