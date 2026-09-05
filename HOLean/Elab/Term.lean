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
hol_prop(⌜p⌝ ∧ True)          -- antiquotation of a `Tm` / `Ty`
```

`#hol` lives in `HOLean.Elab.Command` so this file does not import
`Axiom` (that would cycle with `Connective`).
-/

open Lean Meta Elab

register_option HOLean.inHolElab : Bool := {
  defValue := false
  descr := "internal: true while elaborating hol_ty / hol_tm / hol_prop / hol"
}

namespace HOLean.Elab

/-- Elaborate `stx` with Lean, then translate. -/
def elabLean (stx : Syntax) (expectedType? : Option Expr := none) : TermElabM Expr :=
  withOptions (·.setBool `HOLean.inHolElab true) do
    Term.withoutErrToSorry <| Term.elabTermAndSynthesize stx expectedType?

def elabAsTy (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isProp then
    throwError "HOLean: expected a HOL type, but this is a proposition \
      (use `hol_prop%`)"
  unless type.isSort do
    throwError "HOLean: expected a HOL type{indentExpr e}"
  return (← exprToTy e).toExpr

def elabAsTm (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isSort && !type.isProp then
    throwError "HOLean: expected a HOL term, but this is a type (use `hol_ty%`)"
  return (← exprToTm e).toExpr

def elabAsProp (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx (mkSort 0)
  unless (← Meta.isProp e) do
    throwError "HOLean: expected a proposition{indentExpr e}"
  return (← exprToTm e).toExpr

/-- Dispatch: `Prop` → term, `Type u` → type, otherwise term. -/
def elabBySort (stx : Syntax) : TermElabM Expr := do
  let e ← elabLean stx
  let type ← whnf (← inferType e)
  if type.isProp then
    return (← exprToTm e).toExpr
  else if type.isSort then
    return (← exprToTy e).toExpr
  else
    return (← exprToTm e).toExpr

/-- Splice a `Tm` or `Ty` into a `hol_*` quotation. -/
def elabHolQuote (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  unless (← getBoolOption `HOLean.inHolElab) do
    throwError "HOLean: `⌜·⌝` is only allowed inside `hol_ty` / `hol_tm` / `hol_prop` / `hol`"
  let inner := stx[1]
  let e ← Term.elabTermAndSynthesize inner none
  let ty ← whnf (← inferType e)
  if ← isDefEq ty (mkConst ``Ty) then
    return mkApp (mkConst ``holTyQuote) e
  if ← isDefEq ty (mkConst ``Tm) then
    match expectedType? with
    | none =>
      -- Do not pick `Prop` or an arrow; Lean infers via `CoeFun` / later expected types.
      return mkApp (mkConst ``HolQuoted.mk) e
    | some exp =>
      let exp ← instantiateMVars exp
      -- A `Tm` used as a Lean *type* (`⌜p⌝ → q`) is a proposition.
      let α := if (← whnf exp).isSort then mkSort 0 else exp
      let u ← getLevel α
      let r := mkApp2 (mkConst ``holTmQuote [u]) α e
      Term.ensureHasType expectedType? r
  else
    throwError "HOLean: `⌜·⌝` expected a `Tm` or `Ty`, got{indentExpr e} : {ty}"

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

/-- Antiquotation: splice a `Tm` or `Ty` into `hol_ty` / `hol_tm` / `hol_prop` / `hol`.

```
hol_prop(⌜p⌝ ∧ True)          -- `p : Tm`
hol_ty(⌜α⌝ → Prop)            -- `α : Ty`
hol_tm(fun (x : ⌜α⌝) => ⌜t⌝)
```

`$` is not used, so Lean syntax quotations can still write
`` `(hol_prop(⌜$p⌝ ∧ True)) ``. -/
syntax:max (name := holQuote) "⌜" term "⌝" : term

@[term_elab holQuote]
def elabHolQuote : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  HOLean.Elab.elabHolQuote stx expectedType?
