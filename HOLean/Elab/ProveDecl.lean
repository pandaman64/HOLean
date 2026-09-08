/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import Lean.Util.CollectLevelParams
import HOLean.Prove
import HOLean.Elab.Decl

/-!
# `hdef'` / `htheorem'`

Minimal commands that evaluate a verified `ProveM` script in the current
HOL environment, extract kernel evidence, and register the updated `Env`.
-/

open Lean Meta Elab Command

namespace HOLean.Elab

def thmsOfDecls (decls : Array HolDecl) : List (HOLean.Name × Tm) :=
  decls.foldl (init := []) fun acc d =>
    match d with
    | .thm _ n stmt => acc ++ [(n, stmt)]
    | .defn .. => acc

def defsOfDecls (decls : Array HolDecl) : List (HOLean.Name × Ty × Tm) :=
  decls.foldl (init := []) fun acc d =>
    match d with
    | .defn _ n ty rhs => acc ++ [(n, ty, rhs)]
    | .thm .. => acc

def mkProveCtxExpr (envE wfE connE thmsE defsE : Expr) : MetaM Expr := do
  let hasEq ← mkAppM ``hasEq_of_conn #[connE]
  mkAppOptM ``HOLean.Prove.ProveCtx.mk
    #[some envE, some wfE, some hasEq, some connE, some thmsE, some defsE]

def currentProveCtxExpr : TermElabM Expr := do
  let decls ← getHolDecls
  let cert ← getHolCert
  liftMetaM do
    mkProveCtxExpr
      (envExprFromDecls decls)
      (prevWfExpr cert)
      (prevConnExpr cert)
      (toExpr (thmsOfDecls decls))
      (toExpr (defsOfDecls decls))

def holProveName (leanN : Lean.Name) : Lean.Name :=
  leanN.appendAfter "_prove"

def proveIsOk (runE : Expr) : TermElabM Expr := do
  let ty ← liftMetaM do
    let isOkE ← mkAppM ``HOLean.Prove.isOk #[runE]
    mkEqApp isOkE (mkConst ``Bool.true)
  proveByRfl ty

def addProveScript (name : Lean.Name) (type value : Expr) : CommandElabM Unit := do
  let type ← liftTermElabM <| instantiateMVars type
  let value ← liftTermElabM <| instantiateMVars value
  if type.hasExprMVar || value.hasExprMVar then
    throwError "HOLean: ProveM script still has metavariables"
  let ls := (collectLevelParams (collectLevelParams {} type) value).params
  liftCoreM <| addDecl <| .defnDecl {
    name
    levelParams := ls.toList
    type
    value
    hints := .abbrev
    safety := .safe
  }

syntax (name := hdefPrimeCmd) "hdef' " ident (ppSpace bracketedBinder)*
  (" : " term)? " := " term : command
syntax (name := htheoremPrimeCmd)
  "htheorem' " ident (ppSpace bracketedBinder)* " : " term " := " term : command

def emitHDefCertFromWitness (leanN : Lean.Name) (holN : HOLean.Name)
    (ty : Ty) (rhs : Tm) (witness : Expr) : CommandElabM Unit := do
  let cert ← getHolCert
  let decls ← getHolDecls
  let envBefore := envExprFromDecls decls
  let envAfter :=
    mkApp4 (mkConst ``Env.addDef) envBefore (toExpr holN) (toExpr ty) (toExpr rhs)
  let holNExpr := toExpr holN
  let tyExpr := toExpr ty
  let rhsExpr := toExpr rhs
  let freshProof ← liftTermElabM do
    liftMetaM do mkAppM ``HOLean.Prove.DefWitness.fresh #[witness]
  let hasTypeProof ← liftTermElabM do
    liftMetaM do mkAppM ``HOLean.Prove.DefWitness.typed #[witness]
  let namesProof ← liftTermElabM do
    liftMetaM do mkAppM ``HOLean.Prove.DefWitness.names #[witness]
  let notFreeProof ← liftTermElabM do
    liftMetaM do mkAppM ``HOLean.Prove.DefWitness.notFree #[witness]
  let tyvarsProof ← liftTermElabM do
    liftMetaM do mkAppM ``HOLean.Prove.DefWitness.tyvars #[witness]
  let hasEq ← liftTermElabM do mkHasEqFromConn (prevConnExpr cert)
  let wfProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_wf_addDef)
      #[envBefore, hasEq, holNExpr, tyExpr, rhsExpr, prevWfExpr cert, freshProof,
        hasTypeProof]
  let wfName := certSuffix "_hol_wf" leanN
  addCertThm wfName (mkEnvWfType envAfter) wfProof
  let connProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_conn_addDef)
      #[envBefore, prevConnExpr cert, holNExpr, tyExpr, rhsExpr, freshProof, namesProof]
  let connName := certSuffix "_hol_conn" leanN
  addCertThm connName (mkConnType envAfter) connProof
  let connApp := mkConst connName
  let hasEqAfter ← liftTermElabM do mkHasEqFromConn connApp
  let modelProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_model_addDef)
      #[envBefore, prevConnExpr cert, holNExpr, tyExpr, rhsExpr, prevModelExpr cert,
        freshProof, prevWfExpr cert, hasTypeProof, tyvarsProof, notFreeProof]
  let modelName := certSuffix "_hol_model" leanN
  addCertDef modelName (mkEnvModelType envAfter) modelProof
  let modelApp := mkConst modelName
  let consistentProof ← liftTermElabM do mkConsistentProofM hasEqAfter connApp modelApp
  let consistentName := certSuffix "_hol_consistent" leanN
  addCertThm consistentName (mkNotFalsumType envAfter) consistentProof
  let soundName := certSuffix "_hol_sound" leanN
  let (soundType, soundVal) ← liftTermElabM do mkSoundCert hasEqAfter modelApp
  addCertThm soundName soundType soundVal
  setHolCert {
    wfThm := wfName
    modelThm := modelName
    consistentThm := consistentName
    soundThm := soundName
    connThm := connName
  }

@[command_elab hdefPrimeCmd]
def elabHDefPrime : CommandElab := fun stx => do
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
  let decls ← getHolDecls
  let envE := envExprFromDecls decls
  let ctxE ← liftTermElabM currentProveCtxExpr
  let witness ← liftTermElabM do
    let certE ← liftMetaM do
      mkAppOptM ``HOLean.Prove.certifyDef
        #[some envE, some (toExpr holN), some (toExpr ty), some (toExpr rhs)]
    let runE ← liftMetaM do
      mkAppOptM ``HOLean.Prove.ProveM.run
        #[some envE, none, some certE, some ctxE]
    let hok ← proveIsOk runE
    liftMetaM do
      mkAppOptM ``HOLean.Prove.extractDef
        #[some envE, some ctxE, some (toExpr holN), some (toExpr ty), some (toExpr rhs),
          some hok]
  emitHDefCertFromWitness leanN holN ty rhs witness
  addLeanDefn leanN leanTy leanRhs
  addHolDecl (.defn leanN holN ty rhs)
  logInfo m!"hdef' {holN} : {repr ty}"

def finishHTheoremPrime (leanN : Lean.Name) (holN : HOLean.Name)
    (stmt : Tm) (propType : Expr) (prov : Expr) : CommandElabM Unit := do
  let decls ← getHolDecls
  let cert ← getHolCert
  let envE := envExprFromDecls decls
  let hasEq ← liftTermElabM do mkHasEqFromConn (prevConnExpr cert)
  let hasTypeProof ← liftTermElabM do
    liftMetaM do
      mkAppOptM ``Provable.concl_bool
        #[some envE, some hasEq, none, some (toExpr stmt), some prov]
  let (provVal, provTy) ← liftTermElabM do
    let p ← mkProvInEnvBefore decls prov
    liftMetaM do assertKernelProof p
    let ty ← inferType p
    pure (p, ty)
  addCertThm (holProvName leanN) provTy provVal
  emitHTheoremCertProvable leanN stmt (mkConst (holProvName leanN)) hasTypeProof
  addLeanThmStmt leanN propType
  addHolDecl (.thm leanN holN stmt)
  logInfo m!"htheorem' {holN}"

@[command_elab htheoremPrimeCmd]
def elabHTheoremPrime : CommandElab := fun stx => do
  let short := stx[1].getId
  let binders := binderSyntaxes stx[2]
  let propStx := stx[4]
  let prfStx := stx[6]
  let leanN := (← getCurrNamespace) ++ short
  let holN := holName short
  checkFresh holN leanN
  let decls ← getHolDecls
  let envE := envExprFromDecls decls
  let (tel, closed) ← liftTermElabM do
    let tel ← elabHolTelescope binders propStx decls
    let expected ← liftMetaM do
      let ct := mkApp (mkConst ``HOLean.Prove.CertifiedThm) envE
      mkApp2 (mkConst ``HOLean.Prove.ProveM) envE ct
    let prf ← Term.elabTermAndSynthesize prfStx expected
    let prf ← instantiateMVars prf
    let closed ← liftMetaM do
      mkAppOptM ``HOLean.Prove.Hol.closeTheorem
        #[some envE, some (toExpr tel.stmt), some (toExpr tel.concl),
          some (toExpr tel.hyps), some (toExpr tel.params), some prf]
    pure (tel, closed)
  let scriptN := holProveName leanN
  let proofTy :=
    mkApp (mkConst ``HOLean.Prove.Proof)
      (mkApp3 (mkConst ``Provable) envE mkNilTmList (toExpr tel.stmt))
  let scriptTy := mkApp2 (mkConst ``HOLean.Prove.ProveM) envE proofTy
  addProveScript scriptN scriptTy closed
  let ctxE ← liftTermElabM currentProveCtxExpr
  let (prov, _hok) ← liftTermElabM do
    let runE ← liftMetaM do
      mkAppOptM ``HOLean.Prove.ProveM.run
        #[some envE, some proofTy, some (mkConst scriptN), some ctxE]
    let hok ← proveIsOk runE
    let prov ← liftMetaM do
      mkAppOptM ``HOLean.Prove.extractProvable
        #[some envE, some ctxE, some (toExpr tel.stmt), some (mkConst scriptN), some hok]
    pure (prov, hok)
  finishHTheoremPrime leanN holN tel.stmt tel.propType prov

end HOLean.Elab
