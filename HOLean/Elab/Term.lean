/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Elab.Translate

/-!
# Term elaborators

Surface syntax that looks like Lean 4, elaborated by Lean, then filtered
and translated to HOL:

```
hol_ty(α → Prop)             -- Ty
hol_tm(fun (x : α) => x)     -- Tm
hol_prop(∀ x : α, x = x)     -- Tm of type bool
hol(True)                    -- dispatch on the sort of the Lean type
hol_ty% Prop                 -- tight `%` form (`term:max`)
```

`#hol t` prints the translation and, for terms, `Tm.infer holEnv []`.
-/

open Lean Meta Elab

namespace HOLean.Elab

/-- Elaborate `stx` with Lean, then translate. -/
def elabLean (stx : Syntax) (expectedType? : Option Expr := none) : TermElabM Expr :=
  Term.withoutErrToSorry <| Term.elabTermAndSynthesize stx expectedType?

def elabAsTy (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isProp then
    throwError "HOLean: expected a HOL type, but this is a proposition \
      (use `hol_prop%`)"
  unless type.isSort do
    throwError "HOLean: expected a HOL type{indentExpr e}"
  toExpr <$> exprToTy e

def elabAsTm (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isSort && !type.isProp then
    throwError "HOLean: expected a HOL term, but this is a type (use `hol_ty%`)"
  toExpr <$> exprToTm e

def elabAsProp (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx (mkSort 0)
  unless (← Meta.isProp e) do
    throwError "HOLean: expected a proposition{indentExpr e}"
  toExpr <$> exprToTm e

/-- Dispatch: `Prop` → term, `Type u` → type, otherwise term. -/
def elabBySort (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isProp then
    toExpr <$> exprToTm e
  else if type.isSort then
    toExpr <$> exprToTy e
  else
    toExpr <$> exprToTm e

def holCommand (stx : Syntax) : TermElabM MessageData := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isProp then
    let t ← exprToTm e
    return m!"HOL proposition:{indentD (repr t)}\n\
      infer: {repr (inferHol t)}"
  else if type.isSort then
    let ty ← exprToTy e
    return m!"HOL type:{indentD (repr ty)}"
  else
    let t ← exprToTm e
    return m!"HOL term:{indentD (repr t)}\n\
      infer: {repr (inferHol t)}"

end HOLean.Elab

/-- Elaborate a Lean type into a HOL `Ty`. -/
elab "hol_ty(" t:term ")" : term =>
  HOLean.Elab.elabAsTy t

/-- Elaborate a Lean term into a HOL `Tm`. -/
elab "hol_tm(" t:term ")" : term =>
  HOLean.Elab.elabAsTm t

/-- Elaborate a Lean proposition into a HOL boolean term. -/
elab "hol_prop(" t:term ")" : term =>
  HOLean.Elab.elabAsProp t

/-- Elaborate into `Ty` or `Tm` according to the sort of the Lean type. -/
elab "hol(" t:term ")" : term =>
  HOLean.Elab.elabBySort t

/-- Tight `%` form: only a `term:max` argument, so `hol_ty% Prop = …` parses. -/
elab:max "hol_ty%" t:term:max : term =>
  HOLean.Elab.elabAsTy t

elab:max "hol_tm%" t:term:max : term =>
  HOLean.Elab.elabAsTm t

elab:max "hol_prop%" t:term:max : term =>
  HOLean.Elab.elabAsProp t

elab:max "hol%" t:term:max : term =>
  HOLean.Elab.elabBySort t

/-- Print the HOL translation of a Lean4-like term, type, or proposition. -/
elab "#hol " t:term : command => do
  let msg ← Lean.Elab.Command.liftTermElabM (HOLean.Elab.holCommand t)
  Lean.logInfo msg
