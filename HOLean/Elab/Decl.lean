/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean.Util.CollectLevelParams
import HOLean.Elab.Term
import HOLean.Elab.Kernel

/-!
# `hdef` / `htheorem`

Both commands extend the current HOL environment stored in
`holStateExt`.

* `hdef c : τ := rhs` — type-check `rhs` at `τ` and `Env.addDef`
* `htheorem n : p := script` — run a `HolM Thm` script (Lean
  metaprogram / kernel combinators) and install `p` as an axiom

A tactic language can replace the script later; for now the body is an
ordinary Lean term of type `HolM Thm`.
-/

open Lean Meta Elab Command

namespace HOLean.Elab

def HolDecl.apply (env : Env) : HolDecl → Env
  | .defn _ n ty rhs => env.addDef n ty rhs
  | .thm _ _ stmt => env.addAxiom stmt

/-- Current HOL environment: `holEnv` plus user `hdef` / `htheorem`. -/
def currentHolEnv [Monad m] [MonadEnv m] : m Env := do
  return (← getHolDecls).foldl HolDecl.apply holEnv

def currentHolCtx [Monad m] [MonadEnv m] : m HolCtx := do
  let decls ← getHolDecls
  return { env := decls.foldl HolDecl.apply holEnv, decls }

def tyvarsOk (ty : Ty) (rhs : Tm) : Bool :=
  rhs.tyvars.all fun x => x ∈ ty.tyvars

unsafe def evalHolMThm (expected e : Expr) : MetaM (HolM Thm) :=
  Meta.evalExpr (HolM Thm) expected e

def checkFresh (holN : HOLean.Name) (leanN : Lean.Name) : CommandElabM Unit := do
  if (← getEnv).find? leanN |>.isSome then
    throwError "HOLean: Lean name `{leanN}` is already declared"
  let env ← currentHolEnv
  if env.constants holN |>.isSome then
    throwError "HOLean: constant `{holN}` is already declared"
  if holNameTaken (← getHolDecls) holN then
    throwError "HOLean: name `{holN}` is already declared"

def addLeanDefn (leanN : Lean.Name) (type value : Expr) : CommandElabM Unit := do
  let type ← liftTermElabM <| instantiateMVars type
  let value ← liftTermElabM <| instantiateMVars value
  if type.hasExprMVar || value.hasExprMVar then
    throwError "HOLean: definition still has metavariables"
  let ls := (collectLevelParams (collectLevelParams {} type) value).params
  liftCoreM <| addDecl <| .defnDecl {
    name := leanN
    levelParams := ls.toList
    type
    value
    hints := .opaque
    safety := .safe
  }

/-- Lean name suffix for the checked `Thm` value of an `htheorem`. -/
def holThmValName (leanN : Lean.Name) : Lean.Name :=
  leanN.appendAfter "_hthm"

def addLeanThmStmt (leanN : Lean.Name) (propType : Expr) : CommandElabM Unit := do
  let propType ← liftTermElabM <| instantiateMVars propType
  if propType.hasExprMVar then
    throwError "HOLean: theorem statement still has metavariables"
  let ls := (collectLevelParams {} propType).params
  liftCoreM <| addDecl <| .axiomDecl {
    name := leanN
    levelParams := ls.toList
    type := propType
    isUnsafe := false
  }

def addLeanThmVal (leanN : Lean.Name) (thm : Thm) : CommandElabM Unit := do
  let valN := holThmValName leanN
  let type := mkConst ``Thm
  let value := toExpr thm
  liftCoreM <| addDecl <| .defnDecl {
    name := valN
    levelParams := []
    type
    value
    hints := .abbrev
    safety := .safe
  }

syntax (name := hdefCmd) "hdef " ident (" : " term)? " := " term : command
syntax (name := htheoremCmd) "htheorem " ident " : " term " := " term : command
syntax (name := holEnvCmd) "#hol_env" : command

@[command_elab hdefCmd]
def elabHDef : CommandElab := fun stx => do
  match stx with
  | `(hdef $n:ident $[ : $tyStx]? := $rhsStx) =>
    let short := n.getId
    let leanN := (← getCurrNamespace) ++ short
    let holN := holName short
    checkFresh holN leanN
    let (ty, rhs, leanTy, leanRhs) ← liftTermElabM do
      let (leanTy, leanRhs) ←
        match tyStx with
        | some tyStx => do
          let leanTy ← elabLean tyStx
          let leanRhs ← elabLean rhsStx leanTy
          pure (leanTy, leanRhs)
        | none => do
          let leanRhs ← elabLean rhsStx
          let leanTy ← inferType leanRhs
          pure (leanTy, leanRhs)
      let leanTy ← instantiateMVars leanTy
      let leanRhs ← instantiateMVars leanRhs
      let ty ← exprToTy leanTy
      let rhs ← exprToTm leanRhs
      pure (ty, rhs, leanTy, leanRhs)
    let env ← currentHolEnv
    match rhs.infer env [] with
    | none =>
      throwError "HOLean: definition RHS is not well-typed in the current environment"
    | some α =>
      unless α == ty do
        throwError "HOLean: RHS has type {repr α}, expected {repr ty}"
    unless rhs.LC 0 do
      throwError "HOLean: definition RHS is not locally closed"
    unless tyvarsOk ty rhs do
      throwError "HOLean: type variables of the RHS must occur in the declared type"
    addLeanDefn leanN leanTy leanRhs
    addHolDecl (.defn leanN holN ty rhs)
    logInfo m!"hdef {holN} : {repr ty}"
  | _ => throwUnsupportedSyntax

@[command_elab htheoremCmd]
unsafe def elabHTheorem : CommandElab := fun stx => do
  match stx with
  | `(htheorem $n:ident : $propStx := $prfStx) =>
    let short := n.getId
    let leanN := (← getCurrNamespace) ++ short
    let holN := holName short
    checkFresh holN leanN
    let (stmt, propType, thm) ← liftTermElabM do
      let e ← elabLean propStx (mkSort 0)
      unless (← Meta.isProp e) do
        throwError "HOLean: expected a proposition{indentExpr e}"
      let propType ← instantiateMVars (← inferType e)
      let stmt ← exprToTm e
      let env ← currentHolEnv
      unless stmt.infer env [] == some .bool do
        throwError "HOLean: statement is not a closed boolean"
      unless stmt.LC 0 do
        throwError "HOLean: statement is not locally closed"
      let expected ← Term.elabTerm (← `(HolM Thm)) none
      let prf ← Term.withoutErrToSorry <| Term.elabTermAndSynthesize prfStx expected
      let prf ← instantiateMVars prf
      let tac ← evalHolMThm expected prf
      let ctx ← currentHolCtx
      match HolM.run tac ctx with
      | .error msg => throwError "HOLean: {msg}"
      | .ok thm =>
        unless thm.hyps.isEmpty do
          throwError "HOLean: theorem still has hypotheses {repr thm.hyps}"
        unless thm.concl == stmt do
          throwError "HOLean: proved {repr thm.concl}, expected {repr stmt}"
        pure (stmt, propType, thm)
    addLeanThmStmt leanN propType
    addLeanThmVal leanN thm
    addHolDecl (.thm leanN holN stmt)
    logInfo m!"htheorem {holN}"
  | _ => throwUnsupportedSyntax

@[command_elab holEnvCmd]
def elabHolEnv : CommandElab := fun _ => do
  let decls ← getHolDecls
  if decls.isEmpty then
    logInfo "HOL environment: holEnv (no user declarations)"
  else
    let lines := decls.map fun
      | .defn _ n ty _ => s!"def {n} : {repr ty}"
      | .thm _ n _ => s!"thm {n}"
    let body := lines.foldl (init := "") fun acc l => acc ++ "  " ++ l ++ "\n"
    logInfo m!"HOL environment ({decls.size} user declaration(s)):\n{body}"

end HOLean.Elab
