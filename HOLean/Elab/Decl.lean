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

* `hdef c binders : τ := rhs` — Lean-style left binders, then `Env.addDef`
* `htheorem n binders : p := script` — a `HolM CertifiedThm` script or kernel
  `Provable` proof
* `htheorem n binders : p := hby tacs` — indented HOL tactic script
-/

open Lean Meta Elab Command
open Lean.Parser.Term

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

unsafe def evalHolMCertified (expected e : Expr) : MetaM (HolM CertifiedThm) :=
  Meta.evalExpr (HolM CertifiedThm) expected e

def checkFresh (holN : HOLean.Name) (leanN : Lean.Name) : CommandElabM Unit := do
  if (← getEnv).find? leanN |>.isSome then
    throwError "HOLean: Lean name `{leanN}` is already declared"
  let env ← currentHolEnv
  if env.lookup holN |>.isSome then
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
and used to emit WF / model / consistency / soundness certificates. -/
def finishHTheorem (leanN : Lean.Name) (holN : HOLean.Name) (stmt : Tm)
    (propType : Expr) (thm : Thm) (provProof? : Option Expr) : CommandElabM Unit := do
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
    emitHTheoremCertProvable leanN stmt (mkConst (holProvName leanN)) inferProof
  | none =>
    emitHTheoremCertWf leanN stmt
  addLeanThmStmt leanN propType
  addLeanThmVal leanN thm
  addHolDecl (.thm leanN holN stmt)
  logInfo m!"htheorem {holN}"

/-- Left-side telescope of `htheorem`.

Type binders (`{α : Type}`) are schematic HOL type variables.  Term
binders of a non-propositional type are value parameters (later `GEN`).
Binders whose *type* is a proposition are sequent hypotheses (later
`DISCH`). -/
structure HolTelescope where
  stmt : Tm
  propType : Expr
  hyps : List Tm
  params : List (HOLean.Name × Ty)
  concl : Tm

def isHolHypothesisFVar (x : Expr) : MetaM Bool := do
  let ty ← inferType x
  return (← whnf (← inferType ty)).isProp

def HolTelescope.tacState (tel : HolTelescope) : HolTacState :=
  HolTacState.initGoal tel.stmt tel.hyps tel.concl tel.params

def elabHolTelescopeFromFVars (xs : Array Expr) (e : Expr) (decls : HolState) :
    TermElabM HolTelescope := do
  unless (← Meta.isProp e) do
    throwError "HOLean: expected a proposition{indentExpr e}"
  let e ← instantiateMVars e
  let propType ← instantiateMVars (← inferType e)
  let concl ← exprToTmVal e
  let mut hyps : List Tm := []
  let mut params : List (HOLean.Name × Ty) := []
  let mut stmt := concl
  for x in xs do
    let xty ← inferType x
    if ← isTyVarSort xty then
      pure ()
    else if ← isHolHypothesisFVar x then
      hyps := hyps ++ [← exprToTmVal xty]
    else
      let n := holName (← x.fvarId!.getUserName)
      let α ← exprToTyVal xty
      params := params ++ [(n, α)]
  for x in xs.reverse do
    let xty ← inferType x
    if ← isTyVarSort xty then
      pure ()
    else if ← isHolHypothesisFVar x then
      stmt := Tm.imp (← exprToTmVal xty) stmt
    else
      let n := holName (← x.fvarId!.getUserName)
      let α ← exprToTyVal xty
      stmt := Tm.all α (stmt.abstract n α)
  let env := decls.foldl HolDecl.apply holEnv
  unless stmt.infer env [] == some .bool do
    throwError "HOLean: statement is not a closed boolean"
  unless stmt.LC 0 do
    throwError "HOLean: statement is not locally closed"
  unless concl.infer env [] == some .bool do
    throwError "HOLean: conclusion is not a boolean"
  unless concl.LC 0 do
    throwError "HOLean: conclusion is not locally closed"
  pure { stmt, propType, hyps, params, concl }

def elabHolTelescope (binders : Array Syntax) (propStx : Syntax)
    (decls : HolState) : TermElabM HolTelescope :=
  Term.elabBinders binders fun xs => do
    let e ← elabLean propStx (mkSort 0)
    elabHolTelescopeFromFVars xs e decls

/-- Close an executable theorem that proved the *open* sequent of `tel`. -/
def closeThmWithTelescope (tel : HolTelescope) (ct : CertifiedThm) : HolM CertifiedThm := do
  if ct.thm.concl == tel.stmt && ct.thm.hyps.isEmpty then
    return ct
  let mut ct := ct
  if ct.thm.concl == tel.concl then
    for p in tel.hyps.reverse do
      ct ← Hol.disch p ct
    for (n, α) in tel.params.reverse do
      ct ← Hol.gen n α ct
  return ct

def binderSyntaxes (stx : Syntax) : Array Syntax :=
  stx.getArgs.filter fun s => !s.isAtom && !s.isMissing

def optionalTypeStx (stx : Syntax) : Option Syntax :=
  if stx.isNone || stx.isMissing then none
  else if stx.getNumArgs ≥ 2 then some stx[1]!
  else none

syntax (name := hdefCmd) "hdef " ident (ppSpace bracketedBinder)* (" : " term)? " := " term : command
syntax (name := htheoremHByCmd) (priority := high)
  "htheorem " ident (ppSpace bracketedBinder)* " : " term " := " "hby" holTacSeq : command
syntax (name := htheoremCmd)
  "htheorem " ident (ppSpace bracketedBinder)* " : " term " := " term : command
syntax (name := holEnvCmd) "#hol_env" : command

def finishTacticTheorem (leanN : Lean.Name) (holN : HOLean.Name)
    (stmt : Tm) (propType : Expr) (ct : CertifiedThm) : CommandElabM Unit := do
  let decls ← getHolDecls
  let cert ← getHolCert
  if ct.trace.usesAssume || ct.trace.usesDisch then
    if ct.trace.usesAssume then
      logInfo "HOLean: no `_hol_prov` certificate (`hassumption` / ASSUME)"
    else
      logInfo "HOLean: no `_hol_prov` certificate (DISCH of hypotheses is not yet replayed)"
    finishHTheorem leanN holN stmt propType ct.thm none
  else
    let proof ← liftTermElabM do
      elabProvable decls (envExprFromDecls decls) (prevConnExpr cert) stmt ct.trace
    finishHTheorem leanN holN stmt propType ct.thm (some proof)

@[command_elab hdefCmd]
def elabHDef : CommandElab := fun stx => do
  let nStx := stx[1]
  let short := nStx.getId
  let binders := binderSyntaxes stx[2]
  let tyStx := optionalTypeStx stx[3]
  let rhsStx := stx[5]
  let leanN := (← getCurrNamespace) ++ short
  let holN := holName short
  checkFresh holN leanN
  let (ty, rhs, leanTy, leanRhs) ← liftTermElabM do
    Term.elabBinders binders fun xs => do
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
      let fullTy ← mkForallFVars xs leanTy
      let fullRhs ← mkLambdaFVars xs leanRhs
      let ty ← exprToTyVal fullTy
      let rhs ← exprToTmVal fullRhs
      let fullTy ← instantiateMVars fullTy
      let fullRhs ← instantiateMVars fullRhs
      pure (ty, rhs, fullTy, fullRhs)
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

@[command_elab htheoremCmd]
unsafe def elabHTheorem : CommandElab := fun stx => do
  let short := stx[1].getId
  let binders := binderSyntaxes stx[2]
  let propStx := stx[4]
  let prfStx := stx[6]
  let leanN := (← getCurrNamespace) ++ short
  let holN := holName short
  checkFresh holN leanN
  let decls ← getHolDecls
  let (tel, ct?, provProof?) ← liftTermElabM do
    Term.elabBinders binders fun xs => do
      let e ← elabLean propStx (mkSort 0)
      let tel ← elabHolTelescopeFromFVars xs e decls
      let envExpr := envExprFromDecls decls
      let provProof? ← try
        let provTy ← liftMetaM do
          let nil ← Meta.mkListLit (mkConst ``Tm) []
          return mkApp3 (mkConst ``Provable) envExpr nil (toExpr tel.stmt)
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
      let ct? ← match provProof? with
      | some _ =>
        pure none
      | none =>
        let expected ← Term.elabTerm (← `(HolM CertifiedThm)) none
        let prf ← Term.elabTermAndSynthesize prfStx expected
        let prf ← instantiateMVars prf
        let tac ← evalHolMCertified expected prf
        let ctx ← currentHolCtx
        match HolM.run (do closeThmWithTelescope tel (← tac)) ctx with
        | .error msg => throwError "HOLean: {msg}"
        | .ok ct => pure (some ct)
      pure (tel, ct?, provProof?)
  match provProof? with
  | some prov =>
    let thm : Thm := { hyps := [], concl := tel.stmt }
    finishHTheorem leanN holN tel.stmt tel.propType thm (some prov)
  | none =>
    let some ct := ct? | throwError "HOLean: internal: missing certified theorem"
    finishTacticTheorem leanN holN tel.stmt tel.propType ct

@[command_elab htheoremHByCmd]
def elabHTheoremHBy : CommandElab := fun stx => do
  let short := stx[1].getId
  let binders := binderSyntaxes stx[2]
  let propStx := stx[4]
  let tacs := holTacsOfSeq stx[7]
  let goalsRef := if tacs.isEmpty then stx[6] else stx[7]
  let leanN := (← getCurrNamespace) ++ short
  let holN := holName short
  checkFresh holN leanN
  let decls ← getHolDecls
  let tel ← liftTermElabM do
    elabHolTelescope binders propStx decls
  let ctx ← currentHolCtx
  let st ← applyHolTacsLocated tel.tacState tacs ctx
  throwUnsolvedGoals goalsRef st
  let ct ← match HolM.run (finishTacState st) ctx with
  | .error msg => throwError "HOLean: {msg}"
  | .ok ct => pure ct
  finishTacticTheorem leanN holN tel.stmt tel.propType ct

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
