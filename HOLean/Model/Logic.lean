/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Derived
import HOLean.Model.Def

/-!
# Denotations of the defined connectives

Each connective is an `addDef` constant, so a model of `HasConnectives`
interprets it as the Harrison / Andrews expansion.  The lemmas below turn
that into the expected two-valued truth tables, used later to satisfy
η / SELECT / INFINITY and to show `⟦⊥⟧ = zfFalse`.
-/

open ZFSet Classical

namespace HOLean

variable {env : Env} {ρ : TyVal}

theorem HasType.truDef [Env.HasEq env] : HasType env [] Tm.truDef truTy :=
  HasType.truExpand

theorem HasType.falsumDef [Env.HasConnectives env] :
    HasType env [] Tm.falsumDef falsumTy :=
  HasType.all (HasType.lam (HasType.bvar (by simp)))

theorem HasType.notDef [Env.HasConnectives env] :
    HasType env [] Tm.notDef notTy :=
  HasType.lam (HasType.imp (HasType.bvar (by simp)) HasType.falsum)

theorem HasType.orDef [Env.HasConnectives env] :
    HasType env [] Tm.orDef orTy := by
  unfold Tm.orDef orTy
  refine HasType.lam (HasType.lam ?_)
  refine HasType.all (HasType.lam ?_)
  refine HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp))) ?_
  exact HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
    (HasType.bvar (by simp))

theorem HasType.exDef [Env.HasConnectives env] :
    HasType env [] Tm.exDef exTy := by
  unfold Tm.exDef exTy
  refine HasType.lam ?_
  refine HasType.all (HasType.lam ?_)
  refine HasType.imp ?_ (HasType.bvar (by simp))
  refine HasType.all (HasType.lam ?_)
  exact HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
    (HasType.bvar (by simp))

theorem HasType.oneOneDef [Env.HasConnectives env] :
    HasType env [] Tm.oneOneDef oneOneTy := by
  unfold Tm.oneOneDef oneOneTy
  refine HasType.lam ?_
  refine HasType.all (HasType.lam ?_)
  refine HasType.all (HasType.lam ?_)
  refine HasType.imp ?_ (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp)))
  exact HasType.mkEq
    (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
    (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))

theorem HasType.ontoDef [Env.HasConnectives env] :
    HasType env [] Tm.ontoDef ontoTy := by
  unfold Tm.ontoDef ontoTy
  refine HasType.lam ?_
  refine HasType.all (HasType.lam ?_)
  refine HasType.ex (HasType.lam ?_)
  exact HasType.mkEq (HasType.bvar (by simp))
    (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))

theorem HasType.denote_bool_mem {Γ p} (hp : HasType env Γ p .bool)
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    p.denote I ξ vs.vals ∈ zfBool := by
  simpa [HasType.denote, Ty.denote_bool] using hp.denote_mem I ξ vs

/-- Unfold a monomorphic defining equation `n = rhs`. -/
theorem EnvModel.unfold_mono [Env.HasEq env] (M : EnvModel env ρ)
    {n : Name} {ty rhs : _}
    (hax : env.axioms (Tm.mkEq ty (.const n ty) rhs))
    (hc : HasType env [] (.const n ty) ty)
    (hr : HasType env [] rhs ty) (ξ : FVarVal ρ) :
    (Tm.const n ty).denote M.interp ξ [] = rhs.denote M.interp ξ [] :=
  (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hc hr).1 (M.ax_denote hax ξ)

/-- Unfold a schematic defining equation at a type instance `ty.inst θ`. -/
theorem EnvModel.unfold_poly [Env.HasEq env] (M : EnvModel env ρ)
    {n : Name} {ty rhs : _} (θ : TySubst)
    (hax : env.axioms (Tm.mkEq ty (.const n ty) rhs))
    (hc : HasType env [] (.const n ty) ty)
    (hr : HasType env [] rhs ty) (ξ : FVarVal ρ) :
    (Tm.const n (ty.inst θ)).denote M.interp ξ [] =
      (rhs.instTy θ).denote M.interp ξ [] := by
  have hax' := M.ax_ok θ _ hax (ξ.pull θ)
  have heq := (Tm.denote_mkEq_true_iff_nil (M.interp.inst θ) (M.inst θ).eq_ok
    (ξ.pull θ) hc hr).1 hax'
  have hconst :
      (Tm.const n ty).denote (M.interp.inst θ) (ξ.pull θ) [] =
        (Tm.const n (ty.inst θ)).denote M.interp ξ [] := rfl
  have hrhs := (Tm.denote_instTy rhs θ M.interp ξ []).symm
  exact (hconst.symm.trans heq).trans hrhs

/-! ## `T` -/

theorem EnvModel.denote_tru [Env.HasConnectives env] (M : EnvModel env ρ)
    (ξ : FVarVal ρ) (vs : List ZFSet) :
    Tm.tru.denote M.interp ξ vs = zfTrue := by
  rw [Tm.denote_LC0 _ _ _ _ Tm.tru_LC]
  have hunf :=
    EnvModel.unfold_mono M Env.HasConnectives.tru_ax HasType.tru HasType.truDef ξ
  have hid : HasType env [] (.lam .bool (.bvar 0)) (.bool ↝ .bool) :=
    HasType.lam (HasType.bvar (by simp))
  have hexp :=
    (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hid hid).2 rfl
  exact hunf.trans hexp

/-! ## `∧` -/

theorem EnvModel.andExpand_app_left [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ)
    {f : ZFSet} (hf : f ∈ Tm.boolCombTy.denote ρ) :
    zfApp
        ((HasType.lam (HasType.app (HasType.app (HasType.bvar (by simp))
            (hp.shift0 _)) (hq.shift0 _))).denote M.interp ξ vs)
        f =
      zfApp (zfApp f (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
  have := HasType.denote_lam_app
    (HasType.app (HasType.app (HasType.bvar (by simp)) (hp.shift0 _))
      (hq.shift0 _)) M.interp ξ vs hf
  simpa [HasType.denote, Tm.denote, CtxVal.cons, Tm.denote_shift1_cons] using this

theorem EnvModel.andExpand_app_right [Env.HasConnectives env]
    {Γ} (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ)
    {f : ZFSet} (hf : f ∈ Tm.boolCombTy.denote ρ) :
    zfApp
        ((HasType.lam (HasType.app (HasType.app (HasType.bvar (by simp))
            (HasType.tru.shift0 _)) (HasType.tru.shift0 _))).denote M.interp ξ vs)
        f =
      zfApp (zfApp f zfTrue) zfTrue := by
  have := HasType.denote_lam_app
    (HasType.app (HasType.app (HasType.bvar (by simp)) (HasType.tru.shift0 _))
      (HasType.tru.shift0 _)) M.interp ξ vs hf
  simpa [HasType.denote, Tm.denote, CtxVal.cons, Tm.denote_shift1_cons,
    EnvModel.denote_tru, Tm.shift_of_LC0 Tm.tru_LC] using this

theorem EnvModel.andExpand_true_iff [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.andExpand q).denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfTrue ∧
        q.denote M.interp ξ vs.vals = zfTrue := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have hleft : HasType env Γ
      (.lam Tm.boolCombTy (.app (.app (.bvar 0) (p.shift 1 0)) (q.shift 1 0)))
      (Tm.boolCombTy ↝ .bool) :=
    HasType.lam (HasType.app (HasType.app (HasType.bvar (by simp)) (hp.shift0 _))
      (hq.shift0 _))
  have hright : HasType env Γ
      (.lam Tm.boolCombTy (.app (.app (.bvar 0) (Tm.tru.shift 1 0)) (Tm.tru.shift 1 0)))
      (Tm.boolCombTy ↝ .bool) :=
    HasType.lam (HasType.app
      (HasType.app (HasType.bvar (by simp)) (HasType.tru.shift0 _))
      (HasType.tru.shift0 _))
  have hiff := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ hleft hright vs
  refine hiff.trans ?_
  have hfL := mem_funs.1 (by
    simpa [HasType.denote, Ty.denote_arrow] using hleft.denote_mem M.interp ξ vs)
  have hfR := mem_funs.1 (by
    simpa [HasType.denote, Ty.denote_arrow] using hright.denote_mem M.interp ξ vs)
  constructor
  · intro heq
    have hfst : zfFst zfBool zfBool ∈ Tm.boolCombTy.denote ρ :=
      zfFst_mem zfBool zfBool
    have hsnd : zfSnd zfBool zfBool ∈ Tm.boolCombTy.denote ρ :=
      zfSnd_mem zfBool zfBool
    have hpT : p.denote M.interp ξ vs.vals = zfTrue := by
      have hL := EnvModel.andExpand_app_left hp hq M ξ vs hfst
      have hR := EnvModel.andExpand_app_right (Γ := Γ) M ξ vs hfst
      have := (hL.trans (by simp [HasType.denote] at heq ⊢; exact congrArg (zfApp · _) heq)).trans hR.symm
      simpa [HasType.denote, zfFst_app hpB hqB, zfFst_app zfTrue_mem_zfBool zfTrue_mem_zfBool] using this
    have hqT : q.denote M.interp ξ vs.vals = zfTrue := by
      have hL := EnvModel.andExpand_app_left hp hq M ξ vs hsnd
      have hR := EnvModel.andExpand_app_right (Γ := Γ) M ξ vs hsnd
      have := (hL.trans (by simp [HasType.denote] at heq ⊢; exact congrArg (zfApp · _) heq)).trans hR.symm
      simpa [HasType.denote, zfSnd_app hpB hqB, zfSnd_app zfTrue_mem_zfBool zfTrue_mem_zfBool] using this
    exact ⟨hpT, hqT⟩
  · intro ⟨hpT, hqT⟩
    apply zfIsFunc_ext hfL hfR
    intro f hf
    have hL := EnvModel.andExpand_app_left hp hq M ξ vs hf
    have hR := EnvModel.andExpand_app_right (Γ := Γ) M ξ vs hf
    simp [HasType.denote, hpT, hqT] at hL hR
    exact hL.trans hR.symm

theorem EnvModel.denote_and_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const andName andTy).denote M.interp ξ vs =
      Tm.andDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.and_ax HasType.andConst
    HasType.andDef ξ

theorem EnvModel.denote_and [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.and q).denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfTrue ∧
        q.denote M.interp ξ vs.vals = zfTrue := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have hand := EnvModel.denote_and_const M ξ vs.vals
  have hinner :
      HasType env [.bool]
        (.lam .bool (Tm.andExpand (.bvar 1) (.bvar 0))) (.bool ↝ .bool) :=
    HasType.lam (HasType.andExpand (HasType.bvar (by simp)) (HasType.bvar (by simp)))
  have hbody := HasType.andExpand (env := env) (Γ := [.bool, .bool])
    (HasType.bvar (by simp)) (HasType.bvar (by simp))
  have happ1 :=
    HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ) hpB
  have happ2 :=
    HasType.denote_lam_app hbody M.interp ξ
      ((CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB) hqB
  have hval :
      zfApp (zfApp (Tm.andDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) =
        (Tm.andExpand (.bvar 1) (.bvar 0)).denote M.interp ξ
          [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] := by
    simp [HasType.denote, Tm.andDef, CtxVal.nil, CtxVal.cons] at happ1 happ2
    exact happ1 ▸ happ2
  have hterm : (p.and q).denote M.interp ξ vs.vals =
      zfApp (zfApp (Tm.andDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
    simp [Tm.and, Tm.denote, hand]
  have hiff :=
    EnvModel.andExpand_true_iff
      (HasType.bvar (α := .bool) (Γ := [.bool, .bool]) (by simp))
      (HasType.bvar (α := .bool) (Γ := [.bool, .bool]) (by simp))
      M ξ ((CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB |>.cons
        (q.denote M.interp ξ vs.vals) hqB)
  simp [Tm.denote, CtxVal.nil, CtxVal.cons] at hiff
  exact (hterm.trans hval) ▸ hiff

/-! ## `⇒` -/

theorem EnvModel.denote_imp_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const impName impTy).denote M.interp ξ vs =
      Tm.impDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.imp_ax HasType.impConst
    HasType.impDef ξ

theorem EnvModel.denote_imp [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.imp q).denote M.interp ξ vs.vals = zfTrue ↔
      (p.denote M.interp ξ vs.vals = zfTrue →
        q.denote M.interp ξ vs.vals = zfTrue) := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have himp := EnvModel.denote_imp_const M ξ vs.vals
  have hinner :
      HasType env [.bool]
        (.lam .bool (Tm.impExpand (.bvar 1) (.bvar 0))) (.bool ↝ .bool) :=
    HasType.lam (HasType.impExpand (HasType.bvar (by simp)) (HasType.bvar (by simp)))
  have hbody := HasType.impExpand (env := env) (Γ := [.bool, .bool])
    (HasType.bvar (by simp)) (HasType.bvar (by simp))
  have happ1 := HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ) hpB
  have happ2 := HasType.denote_lam_app hbody M.interp ξ
    ((CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB) hqB
  have hval :
      zfApp (zfApp (Tm.impDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) =
        (Tm.impExpand (.bvar 1) (.bvar 0)).denote M.interp ξ
          [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] := by
    simp [HasType.denote, Tm.impDef, CtxVal.nil, CtxVal.cons] at happ1 happ2
    exact happ1 ▸ happ2
  have hterm : (p.imp q).denote M.interp ξ vs.vals =
      zfApp (zfApp (Tm.impDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
    simp [Tm.imp, Tm.denote, himp]
  have hp' : HasType env [.bool, .bool] (.bvar 1) .bool := HasType.bvar (by simp)
  have hq' : HasType env [.bool, .bool] (.bvar 0) .bool := HasType.bvar (by simp)
  have vs' :
      CtxVal ρ [.bool, .bool] :=
    (CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB |>.cons
      (q.denote M.interp ξ vs.vals) hqB
  have hiff :=
    Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ (HasType.and hp' hq') hp' vs'
  have hand := EnvModel.denote_and hp' hq' M ξ vs'
  have handB := (HasType.and hp' hq').denote_bool_mem M.interp ξ vs'
  simp [Tm.impExpand, Tm.denote, CtxVal.nil, CtxVal.cons, HasType.denote] at hiff hand handB
  have hpq :
      (Tm.impExpand (.bvar 1) (.bvar 0)).denote M.interp ξ
          [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] = zfTrue ↔
        (p.denote M.interp ξ vs.vals = zfTrue →
          q.denote M.interp ξ vs.vals = zfTrue) :=
    hiff.trans (zfBool_imp_from_and hpB handB hand)
  exact (hterm.trans hval) ▸ hpq

/-! ## `∀` -/

theorem Tm.exTy_inst (α : Ty) :
    exTy.inst [(primTyVar, α)] = (α ↝ .bool) ↝ .bool := by
  simp [exTy, primTyVar, Ty.inst, TySubst.lookup]

theorem Tm.oneOneTy_inst (α β : Ty) :
    oneOneTy.inst [(primTyVar, α), (primTyVarB, β)] = (α ↝ β) ↝ .bool := by
  simp [oneOneTy, primTyVar, primTyVarB, Ty.inst, TySubst.lookup]

theorem Tm.ontoTy_inst (α β : Ty) :
    ontoTy.inst [(primTyVar, α), (primTyVarB, β)] = (α ↝ β) ↝ .bool := by
  simp [ontoTy, primTyVar, primTyVarB, Ty.inst, TySubst.lookup]

theorem Tm.exDef_instTy (α : Ty) :
    Tm.exDef.instTy [(primTyVar, α)] =
      .lam (α ↝ .bool)
        (Tm.all .bool (.lam .bool
          (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
            (.bvar 0)))) := by
  simp [Tm.exDef, Tm.all, Tm.imp, Tm.instTy, Ty.inst, TySubst.lookup, primTyVar,
    allTy, impTy]

theorem Tm.oneOneDef_instTy (α β : Ty) :
    Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)] =
      .lam (α ↝ β)
        (Tm.all α (.lam α
          (Tm.all α (.lam α
            (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
              (Tm.mkEq α (.bvar 1) (.bvar 0))))))) := by
  simp [Tm.oneOneDef, Tm.all, Tm.imp, Tm.mkEq, Tm.eqConst, Tm.instTy, Ty.inst,
    TySubst.lookup, primTyVar, primTyVarB, allTy, impTy]

theorem Tm.ontoDef_instTy (α β : Ty) :
    Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)] =
      .lam (α ↝ β)
        (Tm.all β (.lam β
          (Tm.ex α (.lam α
            (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))))))) := by
  simp [Tm.ontoDef, Tm.all, Tm.ex, Tm.mkEq, Tm.eqConst, Tm.instTy, Ty.inst,
    TySubst.lookup, primTyVar, primTyVarB, allTy, exTy]

theorem EnvModel.denote_lam_tru [Env.HasConnectives env]
    {Γ} (α : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.lam α Tm.tru).denote M.interp ξ vs.vals =
      zfConst (α.denote ρ) zfTrue := by
  apply ext
  intro z
  simp [Tm.denote, zfConst, mem_map]
  constructor
  · intro ⟨x, hx, heq⟩
    refine ⟨x, hx, ?_⟩
    simp [lamFn, hx, EnvModel.denote_tru] at heq ⊢
    exact heq
  · intro ⟨x, hx, heq⟩
    refine ⟨x, hx, ?_⟩
    simp [lamFn, hx, EnvModel.denote_tru] at heq ⊢
    exact heq

theorem EnvModel.allExpand_true_iff [Env.HasConnectives env]
    {Γ α P} (hP : HasType env Γ P (α ↝ .bool))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.allExpand α P).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ x ∈ α.denote ρ, zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
  have hlam := HasType.lam (α := α) (HasType.tru (env := env) (Γ := α :: Γ))
  have hiff := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ hP hlam vs
  have hPmem := mem_funs.1 (by
    simpa [HasType.denote, Ty.denote_arrow] using hP.denote_mem M.interp ξ vs)
  have hTmem := zfConst_isFunc (A := α.denote ρ) (B := zfBool) zfTrue_mem_zfBool
  refine hiff.trans ?_
  constructor
  · intro heq x hx
    have := congrArg (fun f => zfApp f x) heq
    simp [HasType.denote, EnvModel.denote_lam_tru, zfConst_app hx] at this
    exact this
  · intro hall
    apply zfIsFunc_ext hPmem hTmem
    intro x hx
    simp [HasType.denote, EnvModel.denote_lam_tru, zfConst_app hx, hall x hx]

theorem EnvModel.denote_all_const [Env.HasConnectives env]
    (α : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const allName ((α ↝ .bool) ↝ .bool)).denote M.interp ξ vs =
      (Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0))).denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  have hunf :=
    EnvModel.unfold_poly M [(primTyVar, α)] Env.HasConnectives.all_ax
      (HasType.allConst (.var primTyVar)) HasType.allDef ξ
  simpa [Tm.allTy_inst, Tm.allDef_instTy] using hunf

theorem EnvModel.denote_all [Env.HasConnectives env]
    {Γ α P} (hP : HasType env Γ P (α ↝ .bool))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.all α P).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ x ∈ α.denote ρ, zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
  have hPmem := hP.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_all_const α M ξ vs.vals
  have hinner : HasType env [α ↝ .bool] (Tm.allExpand α (.bvar 0)) .bool :=
    HasType.allExpand (HasType.bvar (by simp))
  have happ := HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ)
    (by simpa [HasType.denote, Ty.denote_arrow] using hPmem)
  have hval :
      zfApp (Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0)) |>.denote M.interp ξ [])
          (P.denote M.interp ξ vs.vals) =
        (Tm.allExpand α (.bvar 0)).denote M.interp ξ
          [P.denote M.interp ξ vs.vals] := by
    simpa [HasType.denote, CtxVal.nil, CtxVal.cons] using happ
  have hterm : (Tm.all α P).denote M.interp ξ vs.vals =
      zfApp (Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0)) |>.denote M.interp ξ [])
        (P.denote M.interp ξ vs.vals) := by
    simp [Tm.all, Tm.denote, hconst]
  have hP' : HasType env [α ↝ .bool] (.bvar 0) (α ↝ .bool) := HasType.bvar (by simp)
  have vs' : CtxVal ρ [α ↝ .bool] :=
    (CtxVal.nil ρ).cons (P.denote M.interp ξ vs.vals)
      (by simpa [HasType.denote, Ty.denote_arrow] using hPmem)
  have hiff := EnvModel.allExpand_true_iff hP' M ξ vs'
  simp [Tm.denote, CtxVal.nil, CtxVal.cons] at hiff
  exact (hterm.trans hval) ▸ hiff

/-! ## `⊥` and `¬` -/

theorem EnvModel.denote_falsum [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    Tm.falsum.denote M.interp ξ vs = zfFalse := by
  rw [Tm.denote_LC0 _ _ _ _ Tm.falsum_LC]
  have hunf :=
    EnvModel.unfold_mono M Env.HasConnectives.falsum_ax HasType.falsum
      HasType.falsumDef ξ
  have hid : HasType env [] (.lam .bool (.bvar 0)) (.bool ↝ .bool) :=
    HasType.lam (HasType.bvar (by simp))
  have hiff := EnvModel.denote_all hid M ξ (CtxVal.nil ρ)
  have hF : zfApp ((Tm.lam .bool (.bvar 0)).denote M.interp ξ []) zfFalse =
      zfFalse := by
    have := HasType.denote_lam_app (HasType.bvar (α := .bool) (by simp))
      M.interp ξ (CtxVal.nil ρ) zfFalse_mem_zfBool
    simpa [HasType.denote, Tm.denote, CtxVal.nil, CtxVal.cons] using this
  have hne : (Tm.all .bool (.lam .bool (.bvar 0))).denote M.interp ξ [] ≠ zfTrue := by
    intro hT
    have := (hiff.1 hT) zfFalse zfFalse_mem_zfBool
    exact zfFalse_ne_zfTrue (hF ▸ this)
  have hB := HasType.falsumDef.denote_bool_mem M.interp ξ (CtxVal.nil ρ)
  simp [HasType.denote, CtxVal.nil, Tm.falsumDef] at hB
  have : (Tm.all .bool (.lam .bool (.bvar 0))).denote M.interp ξ [] = zfFalse :=
    zfBool_eq_false_of_ne_true hB hne
  exact hunf.trans this

theorem EnvModel.denote_not_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const notName notTy).denote M.interp ξ vs =
      Tm.notDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.not_ax HasType.notConst
    HasType.notDef ξ

theorem EnvModel.denote_not [Env.HasConnectives env]
    {Γ p} (hp : HasType env Γ p .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    p.not.denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfFalse := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hconst := EnvModel.denote_not_const M ξ vs.vals
  have hbody : HasType env [.bool] (Tm.imp (.bvar 0) Tm.falsum) .bool :=
    HasType.imp (HasType.bvar (by simp)) HasType.falsum
  have happ := HasType.denote_lam_app hbody M.interp ξ (CtxVal.nil ρ) hpB
  have hval :
      zfApp (Tm.notDef.denote M.interp ξ []) (p.denote M.interp ξ vs.vals) =
        (Tm.imp (.bvar 0) Tm.falsum).denote M.interp ξ
          [p.denote M.interp ξ vs.vals] := by
    simpa [HasType.denote, Tm.notDef, CtxVal.nil, CtxVal.cons] using happ
  have hterm : p.not.denote M.interp ξ vs.vals =
      zfApp (Tm.notDef.denote M.interp ξ []) (p.denote M.interp ξ vs.vals) := by
    simp [Tm.not, Tm.denote, hconst]
  have hp' : HasType env [.bool] (.bvar 0) .bool := HasType.bvar (by simp)
  have vs' : CtxVal ρ [.bool] :=
    (CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB
  have hiff := EnvModel.denote_imp hp' HasType.falsum M ξ vs'
  simp [Tm.denote, CtxVal.nil, CtxVal.cons, EnvModel.denote_falsum] at hiff
  have hneq : (p.denote M.interp ξ vs.vals = zfTrue → zfFalse = zfTrue) ↔
      p.denote M.interp ξ vs.vals = zfFalse := by
    constructor
    · intro himp
      exact zfBool_eq_false_of_ne_true hpB fun hpT => zfFalse_ne_zfTrue (himp hpT)
    · intro hpF hpT
      exact (zfFalse_ne_zfTrue (hpF ▸ hpT)).elim
  exact (hterm.trans hval) ▸ (hiff.trans hneq)

/-! ## `∨` -/

theorem EnvModel.denote_or_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const orName orTy).denote M.interp ξ vs =
      Tm.orDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.or_ax HasType.orConst
    HasType.orDef ξ

theorem EnvModel.denote_or [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.or q).denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfTrue ∨
        q.denote M.interp ξ vs.vals = zfTrue := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have hor := EnvModel.denote_or_const M ξ vs.vals
  have hinner :
      HasType env [.bool]
        (.lam .bool
          (Tm.all .bool (.lam .bool
            (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
              (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))))))
        (.bool ↝ .bool) :=
    HasType.lam (HasType.all (HasType.lam
      (HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        (HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp))))))
  have hbody :
      HasType env [.bool, .bool]
        (Tm.all .bool (.lam .bool
          (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
            (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))))) .bool :=
    HasType.all (HasType.lam
      (HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        (HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp)))))
  have happ1 := HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ) hpB
  have happ2 := HasType.denote_lam_app hbody M.interp ξ
    ((CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB) hqB
  have hval :
      zfApp (zfApp (Tm.orDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) =
        (Tm.all .bool (.lam .bool
          (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
            (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))))).denote
          M.interp ξ
          [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] := by
    simp [HasType.denote, Tm.orDef, CtxVal.nil, CtxVal.cons] at happ1 happ2
    exact happ1 ▸ happ2
  have hterm : (p.or q).denote M.interp ξ vs.vals =
      zfApp (zfApp (Tm.orDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
    simp [Tm.or, Tm.denote, hor]
  have hP : HasType env [.bool, .bool]
      (.lam .bool
        (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
          (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))))
      (.bool ↝ .bool) :=
    HasType.lam
      (HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        (HasType.imp (HasType.imp (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp))))
  have vs' : CtxVal ρ [.bool, .bool] :=
    (CtxVal.nil ρ).cons (p.denote M.interp ξ vs.vals) hpB |>.cons
      (q.denote M.interp ξ vs.vals) hqB
  have hall := EnvModel.denote_all hP M ξ vs'
  have hbodyT {r : ZFSet} (hr : r ∈ zfBool) :
      zfApp
          ((.lam .bool
            (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
              (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0)))).denote
            M.interp ξ
            [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals])
          r = zfTrue ↔
        (p.denote M.interp ξ vs.vals = zfTrue → r = zfTrue) →
          (q.denote M.interp ξ vs.vals = zfTrue → r = zfTrue) →
            r = zfTrue := by
    have hp2 : HasType env [.bool, .bool, .bool] (.bvar 2) .bool :=
      HasType.bvar (by simp)
    have hq1 : HasType env [.bool, .bool, .bool] (.bvar 1) .bool :=
      HasType.bvar (by simp)
    have hr0 : HasType env [.bool, .bool, .bool] (.bvar 0) .bool :=
      HasType.bvar (by simp)
    have vsr : CtxVal ρ [.bool, .bool, .bool] := vs'.cons r hr
    have happ := HasType.denote_lam_app
      (HasType.imp (HasType.imp hp2 hr0) (HasType.imp (HasType.imp hq1 hr0) hr0))
      M.interp ξ vs' hr
    have himp1 := EnvModel.denote_imp hp2 hr0 M ξ vsr
    have himp2 := EnvModel.denote_imp hq1 hr0 M ξ vsr
    have hmid := EnvModel.denote_imp (HasType.imp hq1 hr0) hr0 M ξ vsr
    have himp3 :=
      EnvModel.denote_imp (HasType.imp hp2 hr0)
        (HasType.imp (HasType.imp hq1 hr0) hr0) M ξ vsr
    simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at
      happ himp1 himp2 hmid himp3
    constructor
    · intro happT hpImp hqImp
      have hprT := himp1.2 hpImp
      have hqrT := himp2.2 hqImp
      have hbodyTrue :
          (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
            (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))).denote
            M.interp ξ vsr.vals = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happ ▸ happT
      have htail := himp3.1 hbodyTrue hprT
      exact hmid.1 htail hqrT
    · intro h
      have hbodyTrue :
          (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
            (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))).denote
            M.interp ξ vsr.vals = zfTrue :=
        himp3.2 fun hprT =>
          hmid.2 fun hqrT => h (himp1.1 hprT) (himp2.1 hqrT)
      simpa [HasType.denote, CtxVal.cons] using happ.symm ▸ hbodyTrue
  have hiff :
      (Tm.all .bool (.lam .bool
          (Tm.imp (Tm.imp (.bvar 2) (.bvar 0))
            (Tm.imp (Tm.imp (.bvar 1) (.bvar 0)) (.bvar 0))))).denote
        M.interp ξ
        [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfTrue ∨
        q.denote M.interp ξ vs.vals = zfTrue := by
    refine hall.trans ?_
    constructor
    · intro h
      by_cases hpT : p.denote M.interp ξ vs.vals = zfTrue
      · exact Or.inl hpT
      · by_cases hqT : q.denote M.interp ξ vs.vals = zfTrue
        · exact Or.inr hqT
        · have hpF := zfBool_eq_false_of_ne_true hpB hpT
          have hqF := zfBool_eq_false_of_ne_true hqB hqT
          have := (hbodyT zfFalse_mem_zfBool).1 (h _ zfFalse_mem_zfBool)
          have : zfFalse = zfTrue := this (fun h' => (hpT h').elim) (fun h' => (hqT h').elim)
          exact (zfFalse_ne_zfTrue this).elim
    · intro hpq r hr
      refine (hbodyT hr).2 ?_
      intro hpT hqT
      match hpq with
      | Or.inl hpT' => exact hpT hpT'
      | Or.inr hqT' => exact hqT hqT'
  exact (hterm.trans hval) ▸ hiff

/-! ## `∃` -/

theorem EnvModel.denote_ex_const [Env.HasConnectives env]
    (α : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const exName ((α ↝ .bool) ↝ .bool)).denote M.interp ξ vs =
      (Tm.exDef.instTy [(primTyVar, α)]).denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  have hunf :=
    EnvModel.unfold_poly M [(primTyVar, α)] Env.HasConnectives.ex_ax
      (HasType.exConst (.var primTyVar)) HasType.exDef ξ
  simpa [Tm.exTy_inst] using hunf

theorem EnvModel.denote_ex [Env.HasConnectives env]
    {Γ α P} (hP : HasType env Γ P (α ↝ .bool))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.ex α P).denote M.interp ξ vs.vals = zfTrue ↔
      ∃ x ∈ α.denote ρ, zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
  have hPmem := hP.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_ex_const α M ξ vs.vals
  have hinner : HasType env [α ↝ .bool]
      (Tm.all .bool (.lam .bool
        (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
          (.bvar 0)))) .bool := by
    refine HasType.all (HasType.lam ?_)
    refine HasType.imp ?_ (HasType.bvar (by simp))
    refine HasType.all (HasType.lam ?_)
    exact HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
      (HasType.bvar (by simp))
  have happ := HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ)
    (by simpa [HasType.denote, Ty.denote_arrow] using hPmem)
  have hval :
      zfApp ((Tm.exDef.instTy [(primTyVar, α)]).denote M.interp ξ [])
          (P.denote M.interp ξ vs.vals) =
        (Tm.all .bool (.lam .bool
          (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
            (.bvar 0)))).denote M.interp ξ
          [P.denote M.interp ξ vs.vals] := by
    simpa [HasType.denote, Tm.exDef_instTy, CtxVal.nil, CtxVal.cons] using happ
  have hterm : (Tm.ex α P).denote M.interp ξ vs.vals =
      zfApp ((Tm.exDef.instTy [(primTyVar, α)]).denote M.interp ξ [])
        (P.denote M.interp ξ vs.vals) := by
    simp [Tm.ex, Tm.denote, hconst]
  have vsP : CtxVal ρ [α ↝ .bool] :=
    (CtxVal.nil ρ).cons (P.denote M.interp ξ vs.vals)
      (by simpa [HasType.denote, Ty.denote_arrow] using hPmem)
  have hQ : HasType env [α ↝ .bool]
      (.lam .bool
        (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
          (.bvar 0)))
      (.bool ↝ .bool) :=
    HasType.lam (HasType.imp
      (HasType.all (HasType.lam
        (HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp)))))
      (HasType.bvar (by simp)))
  have hall := EnvModel.denote_all hQ M ξ vsP
  have hbody {q : ZFSet} (hq : q ∈ zfBool) :
      zfApp
          ((.lam .bool
            (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
              (.bvar 0))).denote M.interp ξ [P.denote M.interp ξ vs.vals])
          q = zfTrue ↔
        ((∀ x ∈ α.denote ρ,
            zfApp (P.denote M.interp ξ vs.vals) x = zfTrue → q = zfTrue) →
          q = zfTrue) := by
    have vsq : CtxVal ρ [.bool, α ↝ .bool] := vsP.cons q hq
    have happq := HasType.denote_lam_app
      (HasType.imp
        (HasType.all (HasType.lam
          (HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
            (HasType.bvar (by simp)))))
        (HasType.bvar (by simp)))
      M.interp ξ vsP hq
    have hallx := EnvModel.denote_all
      (HasType.lam (α := α)
        (HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp))))
      M ξ vsq
    have himp := EnvModel.denote_imp
      (HasType.all (HasType.lam
        (HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp)))))
      (HasType.bvar (α := .bool) (Γ := [.bool, α ↝ .bool]) (by simp))
      M ξ vsq
    have hxT {x : ZFSet} (hx : x ∈ α.denote ρ) :
        zfApp
            ((.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))).denote
              M.interp ξ vsq.vals)
            x = zfTrue ↔
          (zfApp (P.denote M.interp ξ vs.vals) x = zfTrue → q = zfTrue) := by
      have vsx : CtxVal ρ [α, .bool, α ↝ .bool] := vsq.cons x hx
      have happx := HasType.denote_lam_app
        (HasType.imp (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.bvar (by simp)))
        M.interp ξ vsq hx
      have himpx := EnvModel.denote_imp
        (HasType.app (α := α) (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        (HasType.bvar (α := .bool) (Γ := [α, .bool, α ↝ .bool]) (by simp))
        M ξ vsx
      simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at happx himpx
      constructor
      · intro happT hpT
        have hbodyTrue :
            (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1)).denote
              M.interp ξ vsx.vals = zfTrue := by
          simpa [HasType.denote, CtxVal.cons] using happx ▸ happT
        exact himpx.1 hbodyTrue (by simpa [HasType.denote, Tm.denote, CtxVal.cons] using hpT)
      · intro himp
        have hbodyTrue :
            (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1)).denote
              M.interp ξ vsx.vals = zfTrue :=
          himpx.2 fun hpT => himp (by simpa [HasType.denote, Tm.denote, CtxVal.cons] using hpT)
        simpa [HasType.denote, CtxVal.cons] using happx.symm ▸ hbodyTrue
    simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at happq hallx himp
    constructor
    · intro happT hallq
      have hbodyTrue :
          (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
            (.bvar 0)).denote M.interp ξ vsq.vals = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happq ▸ happT
      refine himp.1 hbodyTrue ?_
      refine hallx.2 ?_
      intro x hx
      exact (hxT hx).2 (hallq x hx)
    · intro himpq
      have hbodyTrue :
          (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
            (.bvar 0)).denote M.interp ξ vsq.vals = zfTrue :=
        himp.2 fun hallT =>
          himpq fun x hx => (hxT hx).1 (hallx.1 hallT x hx)
      simpa [HasType.denote, CtxVal.cons] using happq.symm ▸ hbodyTrue
  have hiff :
      (Tm.all .bool (.lam .bool
        (Tm.imp (Tm.all α (.lam α (Tm.imp ((.bvar 2).app (.bvar 0)) (.bvar 1))))
          (.bvar 0)))).denote M.interp ξ
        [P.denote M.interp ξ vs.vals] = zfTrue ↔
      ∃ x ∈ α.denote ρ, zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
    refine hall.trans ?_
    constructor
    · intro h
      by_contra hex
      have hnone : ∀ x ∈ α.denote ρ,
          ¬ zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
        intro x hx hpT
        exact hex ⟨x, hx, hpT⟩
      have hF := (hbody zfFalse_mem_zfBool).1 (h _ zfFalse_mem_zfBool)
      have : zfFalse = zfTrue :=
        hF fun x hx hpT => (hnone x hx hpT).elim
      exact zfFalse_ne_zfTrue this
    · intro ⟨x, hx, hpT⟩ q hq
      refine (hbody hq).2 ?_
      intro hallq
      exact hallq x hx hpT
  exact (hterm.trans hval) ▸ hiff

/-! ## `ONE_ONE` / `ONTO` -/

theorem EnvModel.denote_oneOne_const [Env.HasConnectives env]
    (α β : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const oneOneName ((α ↝ β) ↝ .bool)).denote M.interp ξ vs =
      (Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  have hunf :=
    EnvModel.unfold_poly M [(primTyVar, α), (primTyVarB, β)]
      Env.HasConnectives.oneOne_ax
      (HasType.oneOneConst (.var primTyVar) (.var primTyVarB)) HasType.oneOneDef ξ
  simpa [Tm.oneOneTy_inst] using hunf

theorem EnvModel.denote_oneOne [Env.HasConnectives env]
    {Γ α β f} (hf : HasType env Γ f (α ↝ β))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.oneOne α β f).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ x ∈ α.denote ρ, ∀ y ∈ α.denote ρ,
        zfApp (f.denote M.interp ξ vs.vals) x =
          zfApp (f.denote M.interp ξ vs.vals) y → x = y := by
  have hfmem := hf.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_oneOne_const α β M ξ vs.vals
  have hinner : HasType env [α ↝ β]
      (Tm.all α (.lam α
        (Tm.all α (.lam α
          (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
            (Tm.mkEq α (.bvar 1) (.bvar 0))))))) .bool := by
    refine HasType.all (HasType.lam ?_)
    refine HasType.all (HasType.lam ?_)
    exact HasType.imp
      (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
      (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp)))
  have happ := HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ)
    (by simpa [HasType.denote, Ty.denote_arrow] using hfmem)
  have hval :
      zfApp ((Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) =
      (Tm.all α (.lam α
        (Tm.all α (.lam α
          (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
            (Tm.mkEq α (.bvar 1) (.bvar 0))))))).denote M.interp ξ
        [f.denote M.interp ξ vs.vals] := by
    simpa [HasType.denote, Tm.oneOneDef_instTy, CtxVal.nil, CtxVal.cons] using happ
  have hterm : (Tm.oneOne α β f).denote M.interp ξ vs.vals =
      zfApp ((Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) := by
    simp [Tm.oneOne, Tm.denote, hconst]
  have vsf : CtxVal ρ [α ↝ β] :=
    (CtxVal.nil ρ).cons (f.denote M.interp ξ vs.vals)
      (by simpa [HasType.denote, Ty.denote_arrow] using hfmem)
  have hxP : HasType env [α ↝ β]
      (.lam α
        (Tm.all α (.lam α
          (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
            (Tm.mkEq α (.bvar 1) (.bvar 0))))))
      (α ↝ .bool) :=
    HasType.lam (HasType.all (HasType.lam
      (HasType.imp
        (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
        (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp))))))
  have hallx := EnvModel.denote_all hxP M ξ vsf
  have hiff := hallx.trans ?_
  · exact (hterm.trans hval) ▸ hiff
  · constructor
    · intro hxall x hx y hy hfxy
      have vsx : CtxVal ρ [α, α ↝ β] := vsf.cons x hx
      have happx := HasType.denote_lam_app
        (HasType.all (HasType.lam
          (HasType.imp
            (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
              (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
            (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp))))))
        M.interp ξ vsf hx
      have hally := EnvModel.denote_all
        (HasType.lam
          (HasType.imp
            (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
              (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
            (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp)))))
        M ξ vsx
      have vsy : CtxVal ρ [α, α, α ↝ β] := vsx.cons y hy
      have happy := HasType.denote_lam_app
        (HasType.imp
          (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
            (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
          (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp))))
        M.interp ξ vsx hy
      have himp := EnvModel.denote_imp
        (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
        (HasType.mkEq (HasType.bvar (α := α) (Γ := [α, α, α ↝ β]) (by simp))
          (HasType.bvar (by simp)))
        M ξ vsy
      have heqL := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
        (HasType.app (α := α) (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        (HasType.app (α := α) (HasType.bvar (by simp)) (HasType.bvar (by simp)))
        vsy
      have heqR := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
        (HasType.bvar (α := α) (Γ := [α, α, α ↝ β]) (by simp))
        (HasType.bvar (by simp)) vsy
      simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at
        happx hally happy himp heqL heqR hxall
      have hxT := hxall x hx
      have hbodyx :
          (Tm.all α (.lam α
            (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
              (Tm.mkEq α (.bvar 1) (.bvar 0))))).denote
            M.interp ξ vsx.vals = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happx ▸ hxT
      have hyT := hally.1 hbodyx y hy
      have hbodyy :
          (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
            (Tm.mkEq α (.bvar 1) (.bvar 0))).denote
            M.interp ξ vsy.vals = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happy ▸ hyT
      have hfEq : (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0))).denote
          M.interp ξ vsy.vals = zfTrue := heqL.2 hfxy
      exact heqR.1 (himp.1 hbodyy hfEq)
    · intro hinj x hx
      have vsx : CtxVal ρ [α, α ↝ β] := vsf.cons x hx
      have happx := HasType.denote_lam_app
        (HasType.all (HasType.lam
          (HasType.imp
            (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
              (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
            (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp))))))
        M.interp ξ vsf hx
      have hally := EnvModel.denote_all
        (HasType.lam
          (HasType.imp
            (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
              (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
            (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp)))))
        M ξ vsx
      have hbodyx :
          (Tm.all α (.lam α
            (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
              (Tm.mkEq α (.bvar 1) (.bvar 0))))).denote
            M.interp ξ vsx.vals = zfTrue := by
        refine hally.2 ?_
        intro y hy
        have vsy : CtxVal ρ [α, α, α ↝ β] := vsx.cons y hy
        have happy := HasType.denote_lam_app
          (HasType.imp
            (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
              (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
            (HasType.mkEq (HasType.bvar (by simp)) (HasType.bvar (by simp))))
          M.interp ξ vsx hy
        have himp := EnvModel.denote_imp
          (HasType.mkEq (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))
            (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
          (HasType.mkEq (HasType.bvar (α := α) (Γ := [α, α, α ↝ β]) (by simp))
            (HasType.bvar (by simp)))
          M ξ vsy
        have heqL := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
          (HasType.app (α := α) (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          (HasType.app (α := α) (HasType.bvar (by simp)) (HasType.bvar (by simp)))
          vsy
        have heqR := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
          (HasType.bvar (α := α) (Γ := [α, α, α ↝ β]) (by simp))
          (HasType.bvar (by simp)) vsy
        simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at happy himp heqL heqR
        have hbodyy :
            (Tm.imp (Tm.mkEq β ((.bvar 2).app (.bvar 1)) ((.bvar 2).app (.bvar 0)))
              (Tm.mkEq α (.bvar 1) (.bvar 0))).denote
              M.interp ξ vsy.vals = zfTrue :=
          himp.2 fun hfxy => heqR.2 (hinj x hx y hy (heqL.1 hfxy))
        simpa [HasType.denote, CtxVal.cons] using happy.symm ▸ hbodyy
      simpa [HasType.denote, CtxVal.cons] using happx.symm ▸ hbodyx

theorem EnvModel.denote_onto_const [Env.HasConnectives env]
    (α β : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const ontoName ((α ↝ β) ↝ .bool)).denote M.interp ξ vs =
      (Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  have hunf :=
    EnvModel.unfold_poly M [(primTyVar, α), (primTyVarB, β)]
      Env.HasConnectives.onto_ax
      (HasType.ontoConst (.var primTyVar) (.var primTyVarB)) HasType.ontoDef ξ
  simpa [Tm.ontoTy_inst] using hunf

theorem EnvModel.denote_onto [Env.HasConnectives env]
    {Γ α β f} (hf : HasType env Γ f (α ↝ β))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.onto α β f).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ y ∈ β.denote ρ, ∃ x ∈ α.denote ρ,
        y = zfApp (f.denote M.interp ξ vs.vals) x := by
  have hfmem := hf.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_onto_const α β M ξ vs.vals
  have hinner : HasType env [α ↝ β]
      (Tm.all β (.lam β
        (Tm.ex α (.lam α (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))))))) .bool :=
    HasType.all (HasType.lam (HasType.ex (HasType.lam
      (HasType.mkEq (HasType.bvar (by simp))
        (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))))))
  have happ := HasType.denote_lam_app hinner M.interp ξ (CtxVal.nil ρ)
    (by simpa [HasType.denote, Ty.denote_arrow] using hfmem)
  have hval :
      zfApp ((Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) =
      (Tm.all β (.lam β
        (Tm.ex α (.lam α (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))))))).denote
        M.interp ξ [f.denote M.interp ξ vs.vals] := by
    simpa [HasType.denote, Tm.ontoDef_instTy, CtxVal.nil, CtxVal.cons] using happ
  have hterm : (Tm.onto α β f).denote M.interp ξ vs.vals =
      zfApp ((Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) := by
    simp [Tm.onto, Tm.denote, hconst]
  have vsf : CtxVal ρ [α ↝ β] :=
    (CtxVal.nil ρ).cons (f.denote M.interp ξ vs.vals)
      (by simpa [HasType.denote, Ty.denote_arrow] using hfmem)
  have hyP : HasType env [α ↝ β]
      (.lam β (Tm.ex α (.lam α (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))))))
      (β ↝ .bool) :=
    HasType.lam (HasType.ex (HasType.lam
      (HasType.mkEq (HasType.bvar (by simp))
        (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))))
  have hally := EnvModel.denote_all hyP M ξ vsf
  have hiff := hally.trans ?_
  · exact (hterm.trans hval) ▸ hiff
  · constructor
    · intro hall y hy
      have vsy : CtxVal ρ [β, α ↝ β] := vsf.cons y hy
      have happy := HasType.denote_lam_app
        (HasType.ex (HasType.lam
          (HasType.mkEq (HasType.bvar (by simp))
            (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))))
        M.interp ξ vsf hy
      have hex := EnvModel.denote_ex
        (HasType.lam
          (HasType.mkEq (HasType.bvar (by simp))
            (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))))
        M ξ vsy
      simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at happy hex hall
      have hyT := hall y hy
      have hbody :
          (Tm.ex α (.lam α (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))))).denote
            M.interp ξ vsy.vals = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happy ▸ hyT
      obtain ⟨x, hx, hpT⟩ := hex.1 hbody
      refine ⟨x, hx, ?_⟩
      have vsx : CtxVal ρ [α, β, α ↝ β] := vsy.cons x hx
      have happx := HasType.denote_lam_app
        (HasType.mkEq (HasType.bvar (by simp))
          (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
        M.interp ξ vsy hx
      have heq := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
        (HasType.bvar (α := β) (Γ := [α, β, α ↝ β]) (by simp))
        (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))) vsx
      simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at happx heq
      have hEqT :
          (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))).denote
            M.interp ξ vsx.vals = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happx ▸ hpT
      exact heq.1 hEqT
    · intro hsurj y hy
      have vsy : CtxVal ρ [β, α ↝ β] := vsf.cons y hy
      have happy := HasType.denote_lam_app
        (HasType.ex (HasType.lam
          (HasType.mkEq (HasType.bvar (by simp))
            (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))))
        M.interp ξ vsf hy
      have hex := EnvModel.denote_ex
        (HasType.lam
          (HasType.mkEq (HasType.bvar (by simp))
            (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp)))))
        M ξ vsy
      obtain ⟨x, hx, hyx⟩ := hsurj y hy
      have vsx : CtxVal ρ [α, β, α ↝ β] := vsy.cons x hx
      have happx := HasType.denote_lam_app
        (HasType.mkEq (HasType.bvar (by simp))
          (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))))
        M.interp ξ vsy hx
      have heq := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
        (HasType.bvar (α := β) (Γ := [α, β, α ↝ β]) (by simp))
        (HasType.app (HasType.bvar (by simp)) (HasType.bvar (by simp))) vsx
      simp [HasType.denote, Tm.denote, CtxVal.cons, CtxVal.nil] at happy hex happx heq
      have hEqT :
          (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))).denote
            M.interp ξ vsx.vals = zfTrue := heq.2 hyx
      have hxT :
          zfApp
              ((.lam α (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0)))).denote
                M.interp ξ vsy.vals)
              x = zfTrue := by
        simpa [HasType.denote, CtxVal.cons] using happx.symm ▸ hEqT
      have hbody :
          (Tm.ex α (.lam α (Tm.mkEq β (.bvar 1) ((.bvar 2).app (.bvar 0))))).denote
            M.interp ξ vsy.vals = zfTrue :=
        hex.2 ⟨x, hx, hxT⟩
      simpa [HasType.denote, CtxVal.cons] using happy.symm ▸ hbody

end HOLean


