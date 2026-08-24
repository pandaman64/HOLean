/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean.Elab.Tactic
import Lean.Util.CollectLevelParams
import HOLean.Axiom
import HOLean.Model.Axiom
import HOLean.Elab.State

/-!
# Soundness / consistency certificates for user environments

Each `hdef` / `htheorem` (with a kernel `Provable` proof) extends the
current HOL environment and emits theorems witnessing WF, a standard
`EnvModel`, consistency, and soundness for the cumulative environment.
-/

open Lean Meta Elab Command

namespace HOLean.Elab

set_option linter.style.haveILetI false

/-- Names of theorems witnessing WF / model / consistency / soundness. -/
structure HolCert where
  wfThm : Lean.Name
  modelThm : Lean.Name
  consistentThm : Lean.Name
  soundThm : Lean.Name
  connThm : Lean.Name
  deriving Inhabited, Repr

def HolCert.holEnv : HolCert := {
  wfThm := `HOLean.holEnv_WF
  modelThm := `HOLean.EnvModel.holEnv_std
  consistentThm := `HOLean.Provable.not_falsum_holEnv
  soundThm := `HOLean.Provable.sound_holEnv
  connThm := `HOLean.instHasConnectivesHolEnv
}

initialize holCertExt : SimplePersistentEnvExtension HolCert HolCert ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun _ c => c
    addImportedFn := fun ass =>
      let flat := ass.foldl (init := #[]) fun acc a => acc ++ a
      match flat with
      | #[] => HolCert.holEnv
      | flat => flat[flat.size - 1]!
  }

def getHolCert [Monad m] [MonadEnv m] : m HolCert := do
  return holCertExt.getState (← getEnv)

def setHolCert [Monad m] [MonadEnv m] (c : HolCert) : m Unit :=
  modifyEnv (holCertExt.addEntry · c)

def certSuffix (suffix : String) (leanN : Lean.Name) : Lean.Name :=
  leanN.appendAfter suffix

def tyvarsOk (ty : Ty) (rhs : Tm) : Bool :=
  rhs.tyvars.all fun x => x ∈ ty.tyvars

theorem tyvarsOk_imp_subset (ty : Ty) (rhs : Tm) (h : tyvarsOk ty rhs = true) :
    ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars := by
  simp [tyvarsOk, List.all_eq_true] at h
  exact h

def holNameNotReserved (n : Name) : Bool :=
  connectiveAndPrimNames.all fun m => n ≠ m

theorem holNameNotReserved_imp (n : Name) (h : holNameNotReserved n = true) :
    nameNotInConnectiveAndPrim n := by
  simp [holNameNotReserved, nameNotInConnectiveAndPrim, List.all_eq_true] at h
  exact h

theorem name_ne_eqName (n : Name) (h : nameNotInConnectiveAndPrim n) : n ≠ eqName :=
  h eqName (by simp [connectiveAndPrimNames])

instance (n : Name) : Decidable (holNameNotReserved n) := by
  dsimp [holNameNotReserved]
  infer_instance

theorem cert_wf_addDef (env : Env) (hasEq : Env.HasEq env) (n : Name) (ty : Ty) (rhs : Tm)
    (hwf : env.WF) (hfresh : env.constants n = none) (hne : n ≠ eqName)
    (hinfer : rhs.infer env [] = some ty) :
    (env.addDef n ty rhs).WF := by
  letI := hasEq
  exact Env.WF.addDef_infer hwf hfresh hne hinfer

theorem cert_conn_addDef (env : Env) (conn : Env.HasConnectives env) (n : Name) (ty : Ty) (rhs : Tm)
    (hfresh : env.constants n = none) (hnames : nameNotInConnectiveAndPrim n) :
    Env.HasConnectives (env.addDef n ty rhs) := by
  letI := conn
  exact Env.HasConnectives.addDef hfresh hnames

noncomputable def cert_model_addDef (env : Env) (conn : Env.HasConnectives env) (n : Name) (ty : Ty) (rhs : Tm)
    (model : EnvModel env TyVal.std) (hfresh : env.constants n = none) (hne : n ≠ eqName)
    (hwf : env.WF) (hinfer : rhs.infer env [] = some ty) (lc : rhs.LC 0 = true)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars) (hfree : ∀ x α, rhs.freeIn x α = false) :
    EnvModel (env.addDef n ty rhs) TyVal.std := by
  letI := conn
  exact EnvModel.addDef_cert n (ty := ty) (rhs := rhs) model TyVal.std_nonempty hfresh hne hwf hinfer lc hvars hfree

theorem cert_wf_addAxiom (env : Env) (hasEq : Env.HasEq env) (hwf : env.WF) (ax : Tm)
    (hinfer : ax.infer env [] = some .bool) :
    (env.addAxiom ax).WF := by
  letI := hasEq
  exact Env.WF.addAxiom_infer hwf ax hinfer

theorem cert_conn_addAxiom (env : Env) (conn : Env.HasConnectives env) (ax : Tm) :
    Env.HasConnectives (env.addAxiom ax) := by
  letI := conn
  exact Env.HasConnectives.addAxiom ax

noncomputable def cert_model_addAxiom (env : Env) (hasEq : Env.HasEq env) (model : EnvModel env TyVal.std)
    (ax : Tm) (hax : [] ⊩[env] ax) :
    EnvModel (env.addAxiom ax) TyVal.std := by
  letI := hasEq
  exact EnvModel.addAxiom_cert model TyVal.std_nonempty ax hax

theorem cert_holEnv_le_thm (env : Env) (stmt : Tm) (h : holEnv.LE env) :
    holEnv.LE (env.addAxiom stmt) :=
  h.trans (Env.LE.addAxiom env stmt)

theorem cert_holEnv_le_def (env : Env) (n : Name) (ty : Ty) (rhs : Tm)
    (hfresh : env.constants n = none) (h : holEnv.LE env) :
    holEnv.LE (env.addDef n ty rhs) :=
  h.trans (Env.LE.addDef_of_fresh hfresh)

theorem cert_prov_weaken {env env' : Env} {p : Tm} (hle : env.LE env') (h : Provable env [] p) :
    Provable env' [] p :=
  Provable.weakenEnv hle h

theorem hasEq_of_conn {env : Env} (conn : Env.HasConnectives env) : Env.HasEq env :=
  inferInstance

theorem cert_denote_falsum {env : Env} (conn : Env.HasConnectives env)
    (M : EnvModel env TyVal.std) (ξ : FVarVal TyVal.std) :
    Tm.falsum.denote M.interp ξ [] = zfFalse := by
  letI := conn
  exact EnvModel.denote_falsum M ξ []

theorem cert_not_falsum {env : Env} (hasEq : Env.HasEq env) (conn : Env.HasConnectives env)
    (M : EnvModel env TyVal.std) :
    ¬ [] ⊩[env] Tm.falsum := by
  letI := hasEq
  letI := conn
  exact Provable.not_falsum_of M TyVal.std_nonempty
    (EnvModel.denote_falsum M (FVarVal.ofNonempty TyVal.std_nonempty) [])

theorem cert_sound_with_model {env : Env} (hasEq : Env.HasEq env)
    (M : EnvModel env TyVal.std) {Γ p}
    (h : Γ ⊩[env] p) (ξ : FVarVal TyVal.std) (hΓ : HypsTrue M.interp ξ Γ) :
    p.denote M.interp ξ [] = zfTrue := by
  letI := hasEq
  exact Provable.sound_with_model M h ξ hΓ

theorem cert_sound {env : Env} (hasEq : Env.HasEq env) (M : EnvModel env TyVal.std) :
    ∀ (Γ : List Tm) (p : Tm), Γ ⊩[env] p →
    ∀ (ξ : FVarVal TyVal.std), HypsTrue M.interp ξ Γ →
    p.denote M.interp ξ [] = zfTrue := by
  intro Γ p h ξ hΓ
  letI := hasEq
  exact Provable.sound_with_model M h ξ hΓ

def envExprFromDecls (decls : Array HolDecl) : Expr :=
  Id.run do
    let mut e := mkConst ``holEnv
    for d in decls do
      match d with
      | .defn _ n ty rhs =>
        e := mkApp4 (mkConst ``Env.addDef) e (toExpr n) (toExpr ty) (toExpr rhs)
      | .thm _ _ stmt =>
        e := mkApp (mkApp (mkConst ``Env.addAxiom) e) (toExpr stmt)
    return e

def mkEqApp (a b : Expr) : MetaM Expr :=
  mkAppM ``Eq #[a, b]

def optTyExpr : Expr :=
  mkApp (mkConst ``Option [Level.zero]) (mkConst ``Ty)

def mkNilTyList : Expr :=
  mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Ty)

def mkNilTmList : Expr :=
  mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Tm)

def mkNilZFSetList : Expr :=
  mkApp (mkConst ``List.nil [Level.one]) (mkConst ``ZFSet [Level.zero])

def mkOptionNone (α : Expr) : Expr :=
  mkApp (mkConst ``Option.none [Level.zero]) α

def mkConstantsNoneType (envExpr holN : Expr) : MetaM Expr := do
  mkEqApp
    (mkApp2 (mkConst ``Env.constants) envExpr holN)
    (mkOptionNone (mkConst ``Ty))

def mkInferSomeType (envExpr rhs ty : Expr) : MetaM Expr := do
  mkEqApp
    (mkApp3 (mkConst ``Tm.infer) envExpr rhs mkNilTyList)
    (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Ty) ty)

def mkInferBoolType (envExpr stmt : Expr) : MetaM Expr :=
  mkInferSomeType envExpr stmt (mkConst ``Ty.bool)

def mkLcTrueType (tm : Expr) : MetaM Expr :=
  mkEqApp (mkApp2 (mkConst ``Tm.LC) tm (mkNatLit 0)) (mkConst ``Bool.true)

def mkTyvarsOkType (ty rhs : Expr) : MetaM Expr :=
  mkEqApp (mkApp2 (mkConst ``HOLean.Elab.tyvarsOk) ty rhs) (mkConst ``Bool.true)

def mkHolNameNotReservedType (holN : Expr) : MetaM Expr :=
  mkEqApp (mkApp (mkConst ``HOLean.Elab.holNameNotReserved) holN) (mkConst ``Bool.true)

def mkEnvWfType (envExpr : Expr) : Expr :=
  mkApp (mkConst ``Env.WF) envExpr

def mkEnvModelType (envExpr : Expr) : Expr :=
  mkApp2 (mkConst ``EnvModel [Level.zero]) envExpr (mkConst ``TyVal.std)

def mkConnType (envExpr : Expr) : Expr :=
  mkApp (mkConst ``Env.HasConnectives) envExpr

def mkNotFalsumType (envExpr : Expr) : Expr :=
  mkApp (mkConst ``Not)
    (mkApp3 (mkConst ``Provable) envExpr mkNilTmList (mkConst ``Tm.falsum))

def runDecideTactic (goalType : Expr) (tac : Syntax) : TermElabM Expr :=
  Term.withoutErrToSorry do
    let mvar ← mkFreshExprMVar goalType
    liftMetaM do
      let (goals, _) ← Lean.Elab.runTactic mvar.mvarId! tac
      unless goals.isEmpty do
        throwError "HOLean: certificate tactic left unsolved goals"
    instantiateMVars mvar

def proveByDecide (type : Expr) : TermElabM Expr := do
  let tac ← `(tactic| decide +native)
  runDecideTactic type tac

def proveNotFree (rhs : Expr) : TermElabM Expr := do
  let type ← liftMetaM do
    withLocalDeclD `x (mkConst ``Name) fun x =>
    withLocalDeclD `α (mkConst ``Ty) fun α => do
      let eq ← mkEqApp (mkApp3 (mkConst ``Tm.freeIn) rhs x α) (mkConst ``Bool.false)
      mkForallFVars #[x, α] eq
  let tac ← `(tactic| intro x α; rfl)
  runDecideTactic type tac

def proveByRfl (type : Expr) : TermElabM Expr := do
  let tac ← `(tactic| rfl)
  runDecideTactic type tac

private def applyHolDecl (env : Env) (d : HolDecl) : Env :=
  match d with
  | .defn _ n ty rhs => env.addDef n ty rhs
  | .thm _ _ stmt => env.addAxiom stmt

private def envFromDecls (decls : Array HolDecl) : Env :=
  decls.foldl applyHolDecl holEnv

def proveInferEq (type : Expr) : TermElabM Expr := do
  proveByDecide type

def proveInferFromDecls (decls : Array HolDecl) (stmt : Tm) : TermElabM Expr := do
  let type ← liftMetaM do mkInferBoolType (envExprFromDecls decls) (toExpr stmt)
  proveInferEq type

def proveInferSomeFromDecls (decls : Array HolDecl) (rhs : Tm) (ty : Ty) : TermElabM Expr := do
  let type ← liftMetaM do
    mkInferSomeType (envExprFromDecls decls) (toExpr rhs) (toExpr ty)
  proveInferEq type

def mkHolEnvLeProof (decls : Array HolDecl) : TermElabM Expr := do
  let mut envExpr := mkConst ``holEnv
  let mut proof := mkApp (mkConst ``Env.LE.refl) envExpr
  for d in decls do
    match d with
    | .defn _ n ty rhs =>
      let holNExpr := toExpr n
      let tyExpr := toExpr ty
      let rhsExpr := toExpr rhs
      let freshTy ← liftMetaM do mkConstantsNoneType envExpr holNExpr
      let freshProof ← proveByRfl freshTy
      proof :=
        mkAppN (mkConst ``HOLean.Elab.cert_holEnv_le_def)
          #[envExpr, holNExpr, tyExpr, rhsExpr, freshProof, proof]
      envExpr := mkApp4 (mkConst ``Env.addDef) envExpr holNExpr tyExpr rhsExpr
    | .thm _ _ stmt =>
      let stmtExpr := toExpr stmt
      proof :=
        mkAppN (mkConst ``HOLean.Elab.cert_holEnv_le_thm)
          #[envExpr, stmtExpr, proof]
      envExpr := mkApp (mkApp (mkConst ``Env.addAxiom) envExpr) stmtExpr
  return proof

def mkProvInEnvBefore (decls : Array HolDecl) (proof : Expr) : TermElabM Expr := do
  let envBefore := envExprFromDecls decls
  let proofTy ← liftMetaM do whnf (← inferType proof)
  let proofEnv? := match proofTy with
    | .app (.app (.app (.const ``Provable _) proofEnv) _) _ => some proofEnv
    | _ => none
  match proofEnv? with
  | some proofEnv =>
    if proofEnv == envBefore then
      return proof
    else if proofEnv == mkConst ``holEnv then
      let hle ← mkHolEnvLeProof decls
      mkAppM ``HOLean.Elab.cert_prov_weaken #[hle, proof]
    else
      throwError "HOLean: kernel proof is relative to a different environment than holEnv"
  | none =>
    throwError "HOLean: expected a kernel `Provable` proof for the certificate"

def addCertThm (name : Lean.Name) (type value : Expr) : CommandElabM Unit := do
  let type ← liftTermElabM <| instantiateMVars type
  let value ← liftTermElabM <| instantiateMVars value
  if type.hasExprMVar || value.hasExprMVar then
    throwError "HOLean: certificate proof still has metavariables"
  let ls := (collectLevelParams (collectLevelParams {} type) value).params
  liftCoreM <| addDecl <| .thmDecl {
    name := name
    levelParams := ls.toList
    type := type
    value := value
  }

def addCertDef (name : Lean.Name) (type value : Expr) : CommandElabM Unit := do
  let type ← liftTermElabM <| instantiateMVars type
  let value ← liftTermElabM <| instantiateMVars value
  if type.hasExprMVar || value.hasExprMVar then
    throwError "HOLean: certificate definition still has metavariables"
  let ls := (collectLevelParams (collectLevelParams {} type) value).params
  liftCoreM <| addDecl <| .defnDecl {
    name := name
    levelParams := ls.toList
    type := type
    value := value
    hints := .opaque
    safety := .safe
  }

def prevModelExpr (cert : HolCert) : Expr :=
  mkConst cert.modelThm

def prevWfExpr (cert : HolCert) : Expr :=
  mkConst cert.wfThm

def prevConnExpr (cert : HolCert) : Expr :=
  mkConst cert.connThm

def mkHasEqFromConn (connExpr : Expr) : MetaM Expr :=
  mkAppM ``HOLean.Elab.hasEq_of_conn #[connExpr]

def mkFalsumDenoteProofM (connInst modelApp : Expr) : MetaM Expr := do
  let ξ ← mkAppM ``FVarVal.ofNonempty #[mkConst ``TyVal.std_nonempty]
  mkAppM ``HOLean.Elab.cert_denote_falsum #[connInst, modelApp, ξ]

def mkConsistentProofM (hasEq connInst modelApp : Expr) : MetaM Expr :=
  mkAppM ``HOLean.Elab.cert_not_falsum #[hasEq, connInst, modelApp]

def mkSoundCert (hasEq modelApp : Expr) : TermElabM (Expr × Expr) := do
  let soundVal ← mkAppM ``HOLean.Elab.cert_sound #[hasEq, modelApp]
  let soundType ← inferType soundVal
  pure (soundType, soundVal)

def emitHDefCert (leanN : Lean.Name) (holN : HOLean.Name) (ty : Ty) (rhs : Tm) : CommandElabM Unit := do
  let cert ← getHolCert
  let decls ← getHolDecls
  let envBefore := envExprFromDecls decls
  let envAfter :=
    mkApp4 (mkConst ``Env.addDef) envBefore (toExpr holN) (toExpr ty) (toExpr rhs)
  let holNExpr := toExpr holN
  let tyExpr := toExpr ty
  let rhsExpr := toExpr rhs
  let freshProof ← liftTermElabM do
    let ty ← liftMetaM do mkConstantsNoneType envBefore holNExpr
    proveByRfl ty
  let namesProof ← liftTermElabM do
    let ty ← liftMetaM do mkHolNameNotReservedType holNExpr
    proveByRfl ty
  let namesImp := Lean.mkAppN (mkConst ``HOLean.Elab.holNameNotReserved_imp) #[holNExpr, namesProof]
  let neEqProof := Lean.mkAppN (mkConst ``HOLean.Elab.name_ne_eqName) #[holNExpr, namesImp]
  let inferProof ← liftTermElabM do
    proveInferSomeFromDecls decls rhs ty
  let lcProof ← liftTermElabM do
    let ty ← liftMetaM do mkLcTrueType rhsExpr
    proveByRfl ty
  let notFreeProof ← liftTermElabM do proveNotFree rhsExpr
  let tyvarsProof ← liftTermElabM do
    let ty ← liftMetaM do mkTyvarsOkType tyExpr rhsExpr
    proveByRfl ty
  let hasEq ← liftTermElabM do mkHasEqFromConn (prevConnExpr cert)
  let wfProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_wf_addDef)
      #[envBefore, hasEq, holNExpr, tyExpr, rhsExpr, prevWfExpr cert, freshProof, neEqProof, inferProof]
  let wfName := certSuffix "_hol_wf" leanN
  addCertThm wfName (mkEnvWfType envAfter) wfProof
  let connProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_conn_addDef)
      #[envBefore, prevConnExpr cert, holNExpr, tyExpr, rhsExpr, freshProof, namesImp]
  let connName := certSuffix "_hol_conn" leanN
  addCertThm connName (mkConnType envAfter) connProof
  let connApp := mkConst connName
  let hasEqAfter ← liftTermElabM do mkHasEqFromConn connApp
  let tyvarsSubset := Lean.mkAppN (mkConst ``HOLean.Elab.tyvarsOk_imp_subset) #[tyExpr, rhsExpr, tyvarsProof]
  let modelProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_model_addDef)
      #[envBefore, prevConnExpr cert, holNExpr, tyExpr, rhsExpr, prevModelExpr cert,
        freshProof, neEqProof, prevWfExpr cert, inferProof, lcProof, tyvarsSubset, notFreeProof]
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

def emitHTheoremCertWf (leanN : Lean.Name) (stmt : Tm) : CommandElabM Unit := do
  let cert ← getHolCert
  let decls ← getHolDecls
  let envBefore := envExprFromDecls decls
  let envAfter := mkApp (mkApp (mkConst ``Env.addAxiom) envBefore) (toExpr stmt)
  let stmtExpr := toExpr stmt
  let hasEq ← liftTermElabM do mkHasEqFromConn (prevConnExpr cert)
  let inferProof ← liftTermElabM do
    proveInferFromDecls decls stmt
  let wfProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_wf_addAxiom)
      #[envBefore, hasEq, prevWfExpr cert, stmtExpr, inferProof]
  let wfName := certSuffix "_hol_wf" leanN
  addCertThm wfName (mkEnvWfType envAfter) wfProof
  let connProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_conn_addAxiom)
      #[envBefore, prevConnExpr cert, stmtExpr]
  let connName := certSuffix "_hol_conn" leanN
  addCertThm connName (mkConnType envAfter) connProof
  setHolCert {
    wfThm := wfName
    modelThm := cert.modelThm
    consistentThm := cert.consistentThm
    soundThm := cert.soundThm
    connThm := connName
  }

def emitHTheoremCertProvable (leanN : Lean.Name) (stmt : Tm) (provProof : Expr)
    (inferProof : Expr) : CommandElabM Unit := do
  let cert ← getHolCert
  let decls ← getHolDecls
  let envBefore := envExprFromDecls decls
  let envAfter := mkApp (mkApp (mkConst ``Env.addAxiom) envBefore) (toExpr stmt)
  let stmtExpr := toExpr stmt
  let hasEq ← liftTermElabM do mkHasEqFromConn (prevConnExpr cert)
  let wfProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_wf_addAxiom)
      #[envBefore, hasEq, prevWfExpr cert, stmtExpr, inferProof]
  let wfName := certSuffix "_hol_wf" leanN
  addCertThm wfName (mkEnvWfType envAfter) wfProof
  let connProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_conn_addAxiom)
      #[envBefore, prevConnExpr cert, stmtExpr]
  let connName := certSuffix "_hol_conn" leanN
  addCertThm connName (mkConnType envAfter) connProof
  let connApp := mkConst connName
  let hasEqAfter ← liftTermElabM do mkHasEqFromConn connApp
  let provInBefore ← liftTermElabM do mkProvInEnvBefore decls provProof
  let modelProof :=
    mkAppN (mkConst ``HOLean.Elab.cert_model_addAxiom)
      #[envBefore, hasEq, prevModelExpr cert, stmtExpr, provInBefore]
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

syntax (name := holCertCmd) "#hol_cert" : command

@[command_elab holCertCmd]
def elabHolCert : CommandElab := fun _ => do
  let cert ← getHolCert
  logInfo m!"HOL certificate:\n  WF: {cert.wfThm}\n  model: {cert.modelThm}\n  \
    consistent: {cert.consistentThm}\n  sound: {cert.soundThm}\n  connectives: {cert.connThm}"

end HOLean.Elab
