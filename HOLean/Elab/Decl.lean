/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean.Util.CollectLevelParams
import HOLean.Elab.Term
import HOLean.Elab.Kernel
import HOLean.Elab.Cert
import HOLean.Elab.Tactic
import HOLean.Elab.Replay

/-!
# `hdef` / `htheorem`

Both commands extend the current HOL environment stored in
`holStateExt`.

* `hdef c : τ := rhs` — type-check `rhs` at `τ` and `Env.addDef`
* `htheorem n : p := script` — run a `HolM Thm` script, a kernel
  `Provable` proof, or (via `by`) a HOL tactic script that records a
  `ProvTrace` and is replayed as `Provable` (backends B and C)
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

/-- Shared finishing steps after a successful `htheorem` proof.

When a kernel `Provable` proof is supplied it is stored as `{leanN}_hol_prov`
and used to emit WF / model / consistency / soundness certificates.  An
optional C-backend proof is stored as `{leanN}_hol_prov_C`. -/
def finishHTheorem (leanN : Lean.Name) (holN : HOLean.Name) (stmt : Tm)
    (propType : Expr) (thm : Thm) (provProof? : Option Expr)
    (provC? : Option Expr := none) : CommandElabM Unit := do
  unless thm.hyps.isEmpty do
    throwError "HOLean: theorem still has hypotheses {repr thm.hyps}"
  unless thm.concl == stmt do
    throwError "HOLean: proved {repr thm.concl}, expected {repr stmt}"
  match provProof? with
  | some prov =>
    let decls ← getHolDecls
    let cert ← getHolCert
    let envE := envExprFromDecls decls
    let connE := prevConnExpr cert
    let (provVal, provTy, inferProof) ← liftTermElabM do
      let p ← mkProvInEnvBefore decls prov
      liftMetaM do assertKernelProof p
      let ty ← inferType p
      let inf ← mkInferBoolProof envE connE stmt
      liftMetaM do assertKernelProof inf
      pure (p, ty, inf)
    addCertThm (holProvName leanN) provTy provVal
    if let some pc := provC? then
      let (cVal, cTy) ← liftTermElabM do
        let p ← instantiateMVars pc
        liftMetaM do assertKernelProof p
        let ty ← inferType p
        pure (p, ty)
      addCertThm (holProvCName leanN) cTy cVal
    emitHTheoremCertProvable leanN stmt (mkConst (holProvName leanN)) inferProof
  | none =>
    emitHTheoremCertWf leanN stmt
  addLeanThmStmt leanN propType
  addLeanThmVal leanN thm
  addHolDecl (.thm leanN holN stmt)
  logInfo m!"htheorem {holN}"

/-- Elaborate the statement of an `htheorem` to a HOL boolean. -/
def elabHTheoremStmt (propStx : Syntax) (decls : HolState) :
    TermElabM (Tm × Expr) := do
  let e ← elabLean propStx (mkSort 0)
  unless (← Meta.isProp e) do
    throwError "HOLean: expected a proposition{indentExpr e}"
  let propType ← instantiateMVars (← inferType e)
  let stmt ← exprToTm e
  let env := decls.foldl HolDecl.apply holEnv
  unless stmt.infer env [] == some .bool do
    throwError "HOLean: statement is not a closed boolean"
  unless stmt.LC 0 do
    throwError "HOLean: statement is not locally closed"
  pure (stmt, propType)

syntax (name := hdefCmd) "hdef " ident (" : " term)? " := " term : command
syntax (name := htheoremCmd) "htheorem " ident " : " term " := " term : command
syntax (name := htheoremByCmd) "htheorem " ident " : " term " by " hol_tac,+ : command
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
    emitHDefCert leanN holN ty rhs
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
    let decls ← getHolDecls
    let (stmt, propType, thm, provProof?) ← liftTermElabM do
      let (stmt, propType) ← elabHTheoremStmt propStx decls
      let envExpr := envExprFromDecls decls
      let provProof? ← try
        let provTy ← liftMetaM do
          let nil ← Meta.mkListLit (mkConst ``Tm) []
          return mkApp3 (mkConst ``Provable) envExpr nil (toExpr stmt)
        let prov ← Term.withoutErrToSorry do
          Term.elabTermAndSynthesize prfStx provTy
        let prov ← instantiateMVars prov
        if prov.hasSorry || prov.hasExprMVar then
          pure none
        else
          let ty ← liftMetaM do inferType prov
          if ty.isAppOf ``Provable then
            pure (some prov)
          else
            pure none
      catch _ =>
        pure none
      let thm ← match provProof? with
      | some _ =>
        pure { hyps := [], concl := stmt }
      | none =>
        let expected ← Term.elabTerm (← `(HolM Thm)) none
        let prf ← Term.elabTermAndSynthesize prfStx expected
        let prf ← instantiateMVars prf
        let tac ← evalHolMThm expected prf
        let ctx ← currentHolCtx
        match HolM.run tac ctx with
        | .error msg => throwError "HOLean: {msg}"
        | .ok thm => pure thm
      pure (stmt, propType, thm, provProof?)
    finishHTheorem leanN holN stmt propType thm provProof?
  | _ => throwUnsupportedSyntax

@[command_elab htheoremByCmd]
def elabHTheoremBy : CommandElab := fun stx => do
  match stx with
  | `(htheorem $n:ident : $propStx by $[$tacs:hol_tac],*) =>
    let short := n.getId
    let leanN := (← getCurrNamespace) ++ short
    let holN := holName short
    checkFresh holN leanN
    let decls ← getHolDecls
    let (stmt, propType) ← liftTermElabM do
      elabHTheoremStmt propStx decls
    let ctx ← currentHolCtx
    let ct ← match evalHolTacProof stmt tacs ctx with
    | .error msg => throwError "HOLean: {msg}"
    | .ok ct => pure ct
    let decls ← getHolDecls
    let cert ← getHolCert
    let envE := envExprFromDecls decls
    let connE := prevConnExpr cert
    let result ← liftTermElabM do
      replayCertified decls envE connE stmt ct.trace
    logInfo m!"htheorem {holN} replay: B size {result.sizeB}, C size {result.sizeC}, \
      C fallback to B: {result.fallbackToB}"
    finishHTheorem leanN holN stmt propType ct.thm (some result.proofB) (some result.proofC)
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
