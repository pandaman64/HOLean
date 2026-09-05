/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Model.Logic

/-!
# Standard model of `holEnv` and consistency

`holEnv` reuses the `holLogic` interpretation of constants and adds the
three HOL Light closed axioms.  η holds because `funs` contains only graphs;
SELECT is `zfChoose`; INFINITY is witnessed by successor on `omega`.

`⟦falsum⟧ = zfFalse`, so `¬ [] ⊩[holEnv] ⊥`.
-/

open ZFSet Classical

namespace HOLean

variable {env : Env} {ρ : TyVal}

private theorem htBvar0 {α : Ty} {Γ} : HasType env (α :: Γ) (Tm.bvar 0) α :=
  HasType.bvar List.getElem?_cons_zero

private theorem htBvar1 {α β : Ty} {Γ} :
    HasType env (α :: β :: Γ) (Tm.bvar 1) β :=
  HasType.bvar (by simp)

/-- Reuse an interpretation when the constant tables agree. -/
def EnvInterp.castConstants {env env' : Env} (I : EnvInterp env ρ)
    (h : env'.constants = env.constants) : EnvInterp env' ρ where
  interp := I.interp
  mem := fun hconst => I.mem (by simpa [Env.lookup, h] using hconst)

theorem EnvInterp.castConstants_interp {env env' : Env} (I : EnvInterp env ρ)
    (h : env'.constants = env.constants) (n : Name) (α : Ty) :
    (I.castConstants (env' := env') h).interp n α = I.interp n α :=
  rfl

/-- Instantiated ETA body: `(λ x. f x) = f` for `f` bound at index 0. -/
private def etaBody (α β : Ty) : Tm :=
  Tm.mkEq (α ↝ β) (.lam α (.app (.bvar 1) (.bvar 0))) (.bvar 0)

private theorem htEtaBody [Env.HasEq env] {α β : Ty} :
    HasType env [α ↝ β] (etaBody α β) .bool :=
  HasType.mkEq
    (HasType.lam (HasType.app (htBvar1 (α := α) (β := α ↝ β)) (htBvar0 (α := α))))
    (htBvar0 (α := α ↝ β))

private theorem etaAxiom_eq_body :
    etaAxiom =
      Tm.all (.var primTyVar ↝ .var primTyVarB)
        (.lam (.var primTyVar ↝ .var primTyVarB)
          (etaBody (.var primTyVar) (.var primTyVarB))) := by
  simpa [etaBody] using etaAxiom_eq

/-- Closed ETA axiom denotes `zfTrue`. -/
theorem EnvModel.denote_eta [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) :
    etaAxiom.denote M.interp ξ [] = zfTrue := by
  rw [etaAxiom_eq_body]
  let A : Ty := .var primTyVar
  let B : Ty := .var primTyVarB
  have hP : HasType env []
      (.lam (A ↝ B) (etaBody A B)) ((A ↝ B) ↝ .bool) :=
    HasType.lam htEtaBody
  have hall := EnvModel.denote_all hP M ξ (CtxVal.nil ρ)
  refine hall.2 ?_
  intro f hfmem
  have happ := Tm.denote_of_lam_app htEtaBody M.interp ξ (CtxVal.nil ρ) hfmem
  have hlam : HasType env [A ↝ B]
      (.lam A (.app (.bvar 1) (.bvar 0))) (A ↝ B) :=
    HasType.lam (HasType.app (htBvar1 (α := A) (β := A ↝ B)) (htBvar0 (α := A)))
  have hb0 : HasType env [A ↝ B] (.bvar 0) (A ↝ B) := htBvar0
  let vs : CtxVal ρ [A ↝ B] := (CtxVal.nil ρ).cons f hfmem
  have hiff := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ hlam hb0 vs
  have hbody : (etaBody A B).denote M.interp ξ vs.vals = zfTrue := by
    refine hiff.2 ?_
    have hfun := mem_funs.1 (by
      simpa [HasType.denote, Ty.denote_arrow] using
        hlam.denote_mem M.interp ξ vs)
    have hfmem' := mem_funs.1 (by
      simpa [HasType.denote, Ty.denote_arrow] using
        hb0.denote_mem M.interp ξ vs)
    apply zfIsFunc_ext hfun hfmem'
    intro x hx
    have happe :=
      Tm.denote_of_lam_app
        (HasType.app (htBvar1 (α := A) (β := A ↝ B) (Γ := [])) (htBvar0 (α := A)))
        M.interp ξ vs hx
    simpa [Tm.denote, Tm.denote_bvar_zero, CtxVal.cons] using happe
  exact happ.symm ▸ hbody

/-- Instantiated SELECT body under binders `P`, `x`. -/
private def selectBody (α : Ty) : Tm :=
  Tm.imp (.app (.bvar 1) (.bvar 0))
    (.app (.bvar 1) (.app (Tm.selectConst α) (.bvar 1)))

private theorem htSelectBody [Env.HasConnectives env] {α : Ty} :
    HasType env [α, α ↝ .bool] (selectBody α) .bool :=
  HasType.imp
    (HasType.app (htBvar1 (α := α) (β := α ↝ .bool)) (htBvar0 (α := α)))
    (HasType.app (htBvar1 (α := α) (β := α ↝ .bool))
      (HasType.app (HasType.selectConst α)
        (htBvar1 (α := α) (β := α ↝ .bool))))

private theorem selectAxiom_eq_body :
    selectAxiom =
      Tm.all (.var primTyVar ↝ .bool)
        (.lam (.var primTyVar ↝ .bool)
          (Tm.all (.var primTyVar)
            (.lam (.var primTyVar) (selectBody (.var primTyVar))))) := by
  simpa [selectBody] using selectAxiom_eq

/-- Closed SELECT axiom denotes `zfTrue`. -/
theorem EnvModel.denote_select [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {hA : ((Ty.var primTyVar).denote ρ).Nonempty}
    (hsel : M.interp.interp selectName
        ((.var primTyVar ↝ .bool) ↝ .var primTyVar) =
      zfSelect ((Ty.var primTyVar).denote ρ) hA) :
    selectAxiom.denote M.interp ξ [] = zfTrue := by
  rw [selectAxiom_eq_body]
  have hinnerTy : HasType env [.var primTyVar ↝ .bool]
      (Tm.all (.var primTyVar)
        (.lam (.var primTyVar) (selectBody (.var primTyVar)))) .bool :=
    HasType.all (HasType.lam htSelectBody)
  have hP : HasType env []
      (.lam (.var primTyVar ↝ .bool)
        (Tm.all (.var primTyVar)
          (.lam (.var primTyVar) (selectBody (.var primTyVar)))))
      ((.var primTyVar ↝ .bool) ↝ .bool) :=
    HasType.lam hinnerTy
  have hallP := EnvModel.denote_all hP M ξ (CtxVal.nil ρ)
  refine hallP.2 ?_
  intro P hPmem
  have happP := Tm.denote_of_lam_app hinnerTy M.interp ξ (CtxVal.nil ρ) hPmem
  let vsP : CtxVal ρ [.var primTyVar ↝ .bool] := (CtxVal.nil ρ).cons P hPmem
  have hallX := EnvModel.denote_all (HasType.lam (htSelectBody (α := .var primTyVar))) M ξ vsP
  have hinner :
      (Tm.all (.var primTyVar)
          (.lam (.var primTyVar) (selectBody (.var primTyVar)))).denote
        M.interp ξ vsP.vals = zfTrue := by
    refine hallX.2 ?_
    intro x hxmem
    have happX :=
      Tm.denote_of_lam_app (htSelectBody (α := .var primTyVar)) M.interp ξ vsP hxmem
    let vs : CtxVal ρ [.var primTyVar, .var primTyVar ↝ .bool] := vsP.cons x hxmem
    have hant : HasType env [.var primTyVar, .var primTyVar ↝ .bool]
        (.app (.bvar 1) (.bvar 0)) .bool :=
      HasType.app
        (htBvar1 (α := .var primTyVar) (β := .var primTyVar ↝ .bool) (Γ := []))
        (htBvar0 (α := .var primTyVar) (Γ := [.var primTyVar ↝ .bool]))
    have hcons : HasType env [.var primTyVar, .var primTyVar ↝ .bool]
        (.app (.bvar 1) (.app (Tm.selectConst (.var primTyVar)) (.bvar 1))) .bool :=
      HasType.app
        (htBvar1 (α := .var primTyVar) (β := .var primTyVar ↝ .bool) (Γ := []))
        (HasType.app (HasType.selectConst (.var primTyVar))
          (htBvar1 (α := .var primTyVar) (β := .var primTyVar ↝ .bool) (Γ := [])))
    have hiff := EnvModel.denote_imp hant hcons M ξ vs
    have hbody :
        (selectBody (.var primTyVar)).denote M.interp ξ vs.vals = zfTrue := by
      have hiff' :
          (selectBody (.var primTyVar)).denote M.interp ξ vs.vals = zfTrue ↔
            ((Tm.app (.bvar 1) (.bvar 0)).denote M.interp ξ vs.vals = zfTrue →
              (Tm.app (.bvar 1)
                  (.app (Tm.selectConst (.var primTyVar)) (.bvar 1))).denote
                M.interp ξ vs.vals = zfTrue) := by
        simpa [selectBody] using hiff
      refine hiff'.2 ?_
      intro hPx
      have hPx' : zfApp P x = zfTrue := by
        simpa [Tm.denote, CtxVal.cons, vs, vsP] using hPx
      have hselApp :
          zfApp ((Tm.selectConst (.var primTyVar)).denote M.interp ξ [x, P]) P =
            zfChoose ((Ty.var primTyVar).denote ρ) hA P := by
        simp [Tm.selectConst, Tm.denote, hsel]
        exact zfSelect_app hA (by simpa [Ty.denote_arrow] using hPmem)
      have hwit := zfChoose_spec hA ⟨x, hxmem, hPx'⟩
      simp [Tm.denote, CtxVal.cons, vs, vsP]
      rw [hselApp]
      exact hwit
    exact happX.symm ▸ hbody
  exact happP.symm ▸ hinner

/-- INFINITY: successor on `omega` is injective and not surjective. -/
theorem EnvModel.denote_infinity [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) :
    infinityAxiom.denote M.interp ξ [] = zfTrue := by
  have hf : HasType env [Ty.ind ↝ Ty.ind] (Tm.bvar 0) (Ty.ind ↝ Ty.ind) :=
    htBvar0 (α := Ty.ind ↝ Ty.ind) (Γ := [])
  have hbody : HasType env [Ty.ind ↝ Ty.ind]
      ((Tm.oneOne .ind .ind (.bvar 0)).and
        (Tm.onto .ind .ind (.bvar 0)).not) .bool :=
    HasType.and (HasType.oneOne hf) (HasType.not (HasType.onto hf))
  have hP : HasType env []
      (.lam (Ty.ind ↝ Ty.ind)
        ((Tm.oneOne .ind .ind (.bvar 0)).and
          (Tm.onto .ind .ind (.bvar 0)).not))
      ((Ty.ind ↝ Ty.ind) ↝ .bool) :=
    HasType.lam hbody
  have hex := EnvModel.denote_ex hP M ξ (CtxVal.nil ρ)
  have hsucc : zfSuccFun ∈ (Ty.ind ↝ Ty.ind).denote ρ :=
    mem_funs.2 zfSuccFun_isFunc
  refine hex.2 ⟨zfSuccFun, hsucc, ?_⟩
  have happ := Tm.denote_of_lam_app hbody M.interp ξ (CtxVal.nil ρ) hsucc
  let vsf : CtxVal ρ [Ty.ind ↝ Ty.ind] :=
    (CtxVal.nil ρ).cons zfSuccFun hsucc
  have hand := EnvModel.denote_and
    (HasType.oneOne hf) (HasType.not (HasType.onto hf)) M ξ vsf
  have hone := EnvModel.denote_oneOne hf M ξ vsf
  have honto := EnvModel.denote_onto hf M ξ vsf
  have hnot := EnvModel.denote_not (HasType.onto hf) M ξ vsf
  have hinj : ∀ x ∈ omega, ∀ y ∈ omega,
      zfApp zfSuccFun x = zfApp zfSuccFun y → x = y := by
    intro x hx y hy hxy
    exact zfSucc_inj ((zfSuccFun_app hx).symm.trans (hxy.trans (zfSuccFun_app hy)))
  have hns : ¬ ∀ y ∈ omega, ∃ x ∈ omega, y = zfApp zfSuccFun x := by
    intro hsurj
    obtain ⟨n, hn, hmiss⟩ := zfSucc_not_surj_omega
    obtain ⟨m, hm, heq⟩ := hsurj n hn
    exact hmiss m hm ((zfSuccFun_app hm).symm.trans heq.symm)
  have hpred :
      ((Tm.oneOne .ind .ind (Tm.bvar 0)).and
        (Tm.onto .ind .ind (Tm.bvar 0)).not).denote M.interp ξ vsf.vals =
        zfTrue :=
    hand.2 ⟨hone.2 hinj, hnot.2 (zfBool_eq_false_of_ne_true
      ((HasType.onto hf).denote_bool_mem M.interp ξ vsf) fun hT =>
        hns (honto.1 hT))⟩
  exact happ.symm ▸ hpred

/-- `holEnv` has the same constants as `holLogic`. -/
theorem holEnv_constants : holEnv.constants = holLogic.constants := by
  simp [holEnv, Env.addAxiom]

/-- Denotation of the three closed HOL axioms in the `holLogic` model. -/
theorem HOLAxiom.denote_holLogic {p} (h : HOLAxiom p)
    {ρ : TyVal} (hρ : ρ.Nonempty) (θ : TySubst) (ξ : FVarVal (ρ.inst θ)) :
    p.denote ((EnvModel.holLogic ρ hρ).interp.inst θ) ξ [] = zfTrue := by
  cases h with
  | eta =>
    exact EnvModel.denote_eta ((EnvModel.holLogic ρ hρ).inst θ) ξ
  | select =>
    have hA : ((Ty.var primTyVar).denote (ρ.inst θ)).Nonempty :=
      Ty.denote_nonempty (TyVal.inst_nonempty hρ θ) (.var primTyVar)
    have hsel :
        ((EnvModel.holLogic ρ hρ).interp.inst θ).interp selectName
            ((.var primTyVar ↝ .bool) ↝ .var primTyVar) =
          zfSelect ((Ty.var primTyVar).denote (ρ.inst θ)) hA := by
      simp only [EnvInterp.inst_interp]
      have h :=
        EnvModel.holLogic_interp_select ρ hρ ((Ty.var primTyVar).inst θ)
      -- `((A↝bool)↝A).inst θ = (A.inst θ ↝ bool) ↝ A.inst θ`
      -- and `⟦A.inst θ⟧ρ = ⟦A⟧(ρ.inst θ)`.
      convert h using 2
      · simp [Ty.inst]
      · exact (Ty.denote_inst ρ θ (.var primTyVar)).symm
    exact EnvModel.denote_select ((EnvModel.holLogic ρ hρ).inst θ) ξ hsel
  | infinity =>
    exact EnvModel.denote_infinity ((EnvModel.holLogic ρ hρ).inst θ) ξ

private theorem holEnv_ax_ok_core {ρ : TyVal} (hρ : ρ.Nonempty) (θ : TySubst)
    (p : Tm) (hp : p ∈ holEnv.axioms) (ξ : FVarVal (ρ.inst θ)) :
    p.denote ((EnvModel.holLogic ρ hρ).interp.inst θ) ξ [] = zfTrue := by
  -- holEnv.axioms = infinity :: select :: eta :: holLogic.axioms
  cases hp with
  | head =>
    exact EnvModel.denote_infinity ((EnvModel.holLogic ρ hρ).inst θ) ξ
  | tail _ hp1 =>
    cases hp1 with
    | head =>
      have hA : ((Ty.var primTyVar).denote (ρ.inst θ)).Nonempty :=
        Ty.denote_nonempty (TyVal.inst_nonempty hρ θ) (.var primTyVar)
      have hsel :
          ((EnvModel.holLogic ρ hρ).interp.inst θ).interp selectName
              ((.var primTyVar ↝ .bool) ↝ .var primTyVar) =
            zfSelect ((Ty.var primTyVar).denote (ρ.inst θ)) hA := by
        simp only [EnvInterp.inst_interp]
        have h :=
          EnvModel.holLogic_interp_select ρ hρ ((Ty.var primTyVar).inst θ)
        convert h using 2
        · simp [Ty.inst]
        · exact (Ty.denote_inst ρ θ (.var primTyVar)).symm
      exact EnvModel.denote_select ((EnvModel.holLogic ρ hρ).inst θ) ξ hsel
    | tail _ hp2 =>
      cases hp2 with
      | head =>
        exact EnvModel.denote_eta ((EnvModel.holLogic ρ hρ).inst θ) ξ
      | tail _ hold =>
        exact (EnvModel.holLogic ρ hρ).ax_ok θ p hold ξ

noncomputable def EnvModel.holEnv (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel holEnv ρ where
  interp := (EnvModel.holLogic ρ hρ).interp.castConstants holEnv_constants
  eq_ok := (EnvModel.holLogic ρ hρ).eq_ok
  ax_ok := fun θ p hp ξ =>
    (Tm.denote_interp_eq_env p
        ((EnvModel.holLogic ρ hρ).interp.inst θ)
        (((EnvModel.holLogic ρ hρ).interp.castConstants holEnv_constants).inst θ)
        ξ [] (fun _ _ => rfl)).symm.trans
      (holEnv_ax_ok_core hρ θ p hp ξ)

/-- Standard nonempty type valuation: every variable is `omega`. -/
def TyVal.std : TyVal.{0} := fun _ => omega

theorem TyVal.std_nonempty : TyVal.std.Nonempty :=
  fun _ => ⟨∅, omega_zero⟩

noncomputable def EnvModel.holEnv_std : EnvModel HOLean.holEnv TyVal.std :=
  EnvModel.holEnv TyVal.std TyVal.std_nonempty

theorem Provable.sound_holEnv {Γ p} (h : Γ ⊩[holEnv] p)
    {ρ : TyVal} (hρ : ρ.Nonempty) (ξ : FVarVal ρ)
    (hΓ : HypsTrue (EnvModel.holEnv ρ hρ).interp ξ Γ) :
    p.denote (EnvModel.holEnv ρ hρ).interp ξ [] = zfTrue :=
  Provable.sound h (EnvModel.holEnv ρ hρ) ξ hΓ

/-- Object-logic falsity is set-theoretic `∅`. -/
theorem EnvModel.holEnv_falsum (ρ : TyVal) (hρ : ρ.Nonempty) (ξ : FVarVal ρ) :
    Tm.falsum.denote (EnvModel.holEnv ρ hρ).interp ξ [] = zfFalse :=
  EnvModel.denote_falsum (EnvModel.holEnv ρ hρ) ξ []

/-- Consistency of the initial HOL environment. -/
theorem Provable.not_falsum_holEnv : ¬ [] ⊩[holEnv] Tm.falsum := by
  intro h
  let ρ : TyVal.{0} := TyVal.std
  have hρ : ρ.Nonempty := TyVal.std_nonempty
  have hT := Provable.sound_holEnv (ρ := ρ) h hρ
    (FVarVal.ofNonempty hρ)
    (fun _ hq => nomatch hq)
  have hF := EnvModel.holEnv_falsum ρ hρ (FVarVal.ofNonempty hρ)
  exact zfFalse_ne_zfTrue (hF ▸ hT)

end HOLean
