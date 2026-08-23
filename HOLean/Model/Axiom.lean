/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Model.Logic

/-!
# Standard model of `holEnv` and consistency

`holEnv` reuses the `holLogic` interpretation of constants and adds the
three HOL Light schemas.  η holds because `funs` contains only graphs;
SELECT is `zfChoose`; INFINITY is witnessed by successor on `omega`.

`⟦falsum⟧ = zfFalse`, so `¬ [] ⊩[holEnv] ⊥`.
-/

open ZFSet Classical

namespace HOLean

variable {env : Env} {ρ : TyVal}

private theorem htBvar0 {α : Ty} {Γ} : HasType env (α :: Γ) (Tm.bvar 0) α :=
  HasType.bvar List.getElem?_cons_zero

/-- Reuse an interpretation when the constant tables agree. -/
def EnvInterp.castConstants {env env' : Env} (I : EnvInterp env ρ)
    (h : env'.constants = env.constants) : EnvInterp env' ρ where
  interp := I.interp
  mem := fun hconst => I.mem (h ▸ hconst)

theorem EnvInterp.castConstants_interp {env env' : Env} (I : EnvInterp env ρ)
    (h : env'.constants = env.constants) (n : Name) (α : Ty) :
    (I.castConstants (env' := env') h).interp n α = I.interp n α :=
  rfl

/-- η: the graph of `λ x. f x` is `f` itself. -/
theorem EnvModel.denote_eta [Env.HasConnectives env]
    {α β f} (hf : HasType env [] f (α ↝ β))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) :
    (etaAxiom α β f).denote M.interp ξ [] = zfTrue := by
  have hbody : HasType env [α] (Tm.app (f.shift 1 0) (Tm.bvar 0)) β :=
    HasType.app (hf.shift0 α) (htBvar0 (α := α) (Γ := []))
  have hlam : HasType env []
      (Tm.lam α (Tm.app (f.shift 1 0) (Tm.bvar 0))) (α ↝ β) :=
    HasType.lam hbody
  have hiff := Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hlam hf
  refine hiff.2 ?_
  have hfmem := mem_funs.1 (by
    simpa [HasType.denote, Ty.denote_arrow] using
      hf.denote_mem M.interp ξ (CtxVal.nil ρ))
  have hfun := mem_funs.1 (by
    simpa [HasType.denote, Ty.denote_arrow] using
      hlam.denote_mem M.interp ξ (CtxVal.nil ρ))
  apply zfIsFunc_ext hfun hfmem
  intro x hx
  have happ := Tm.denote_of_lam_app hbody M.interp ξ (CtxVal.nil ρ) hx
  rw [Tm.denote, Tm.denote_shift1_cons, Tm.denote_bvar_zero] at happ
  exact happ

/-- SELECT: if `P x` then `P (ε P)`. -/
theorem EnvModel.denote_select [Env.HasConnectives env]
    {α P x} (hP : HasType env [] P (α ↝ .bool)) (hx : HasType env [] x α)
    (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {hA : (α.denote ρ).Nonempty}
    (hsel : M.interp.interp selectName ((α ↝ .bool) ↝ α) =
      zfSelect (α.denote ρ) hA) :
    (selectAxiom α P x).denote M.interp ξ [] = zfTrue := by
  have hε : HasType env [] (.app (Tm.selectConst α) P) α :=
    HasType.app (HasType.selectConst α) hP
  have hiff := EnvModel.denote_imp (HasType.app hP hx) (HasType.app hP hε)
    M ξ (CtxVal.nil ρ)
  refine hiff.2 ?_
  intro hPx
  have hPmem := mem_funs.1 (by
    simpa [HasType.denote, Ty.denote_arrow, CtxVal.nil] using
      hP.denote_mem M.interp ξ (CtxVal.nil ρ))
  have hxmem : x.denote M.interp ξ [] ∈ α.denote ρ := by
    simpa [HasType.denote, CtxVal.nil] using hx.denote_mem M.interp ξ (CtxVal.nil ρ)
  have hselApp :
      zfApp (Tm.selectConst α |>.denote M.interp ξ [])
          (P.denote M.interp ξ []) =
        zfChoose (α.denote ρ) hA (P.denote M.interp ξ []) := by
    simp [Tm.selectConst, Tm.denote, hsel]
    exact zfSelect_app hA (mem_funs.2 hPmem)
  have hwit := zfChoose_spec hA
    ⟨x.denote M.interp ξ [], hxmem, by
      simpa [Tm.denote, CtxVal.nil] using hPx⟩
  simp [Tm.denote, CtxVal.nil] at hPx ⊢
  simpa [hselApp] using hwit.2

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
theorem holEnv_constants : holEnv.constants = holLogic.constants := rfl

/-- The three schemas denote `zfTrue` already in the `holLogic` model. -/
theorem HOLAxiom.denote_holLogic {p} (h : HOLAxiom p)
    {ρ : TyVal} (hρ : ρ.Nonempty) (θ : TySubst) (ξ : FVarVal (ρ.inst θ)) :
    p.denote ((EnvModel.holLogic ρ hρ).interp.inst θ) ξ [] = zfTrue := by
  cases h with
  | eta hf =>
    exact EnvModel.denote_eta hf ((EnvModel.holLogic ρ hρ).inst θ) ξ
  | @select α P x hP hx =>
    have hA : (α.denote (ρ.inst θ)).Nonempty :=
      Ty.denote_nonempty (TyVal.inst_nonempty hρ θ) α
    have hsel :
        ((EnvModel.holLogic ρ hρ).interp.inst θ).interp selectName
            ((α ↝ .bool) ↝ α) =
          zfSelect (α.denote (ρ.inst θ)) hA := by
      simp [EnvInterp.inst, EnvModel.holLogic_interp_select, Ty.denote_inst]
    exact EnvModel.denote_select hP hx ((EnvModel.holLogic ρ hρ).inst θ) ξ hsel
  | infinity =>
    exact EnvModel.denote_infinity ((EnvModel.holLogic ρ hρ).inst θ) ξ

noncomputable def EnvModel.holEnv (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel holEnv ρ where
  interp := (EnvModel.holLogic ρ hρ).interp.castConstants holEnv_constants
  eq_ok := (EnvModel.holLogic ρ hρ).eq_ok
  ax_ok := fun θ p hp ξ =>
    match hp with
    | Or.inl hold =>
      (Tm.denote_interp_eq_env p
          ((EnvModel.holLogic ρ hρ).interp.inst θ)
          (((EnvModel.holLogic ρ hρ).interp.castConstants holEnv_constants).inst θ)
          ξ [] (fun _ _ => rfl)).symm.trans
        ((EnvModel.holLogic ρ hρ).ax_ok θ p hold ξ)
    | Or.inr hax =>
      (Tm.denote_interp_eq_env p
          ((EnvModel.holLogic ρ hρ).interp.inst θ)
          (((EnvModel.holLogic ρ hρ).interp.castConstants holEnv_constants).inst θ)
          ξ [] (fun _ _ => rfl)).symm.trans
        (HOLAxiom.denote_holLogic hax hρ θ ξ)

/-- Standard nonempty type valuation: every variable is `omega`. -/
def TyVal.std : TyVal.{0} := fun _ => omega

theorem TyVal.std_nonempty : TyVal.std.Nonempty :=
  fun _ => ⟨∅, omega_zero⟩

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

