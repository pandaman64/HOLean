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

set_option maxHeartbeats 800000

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

private theorem htBvar0 {α : Ty} {Γ} : HasType env (α :: Γ) (Tm.bvar 0) α :=
  HasType.bvar (by simp)

private theorem htBvar1 {γ α : Ty} {Γ} : HasType env (γ :: α :: Γ) (Tm.bvar 1) α :=
  HasType.bvar (by simp)

private theorem htBvar2 {δ γ α : Ty} {Γ} :
    HasType env (δ :: γ :: α :: Γ) (Tm.bvar 2) α :=
  HasType.bvar (by simp)

theorem HasType.exDef [Env.HasConnectives env] :
    HasType env [] Tm.exDef exTy := by
  unfold Tm.exDef exTy
  refine HasType.lam ?_
  refine HasType.all (HasType.lam ?_)
  refine HasType.imp ?_ (HasType.bvar (by simp))
  refine HasType.all (HasType.lam ?_)
  exact HasType.imp (HasType.app (α := .var primTyVar) htBvar2 htBvar0) htBvar1

theorem HasType.oneOneDef [Env.HasConnectives env] :
    HasType env [] Tm.oneOneDef oneOneTy := by
  unfold Tm.oneOneDef oneOneTy
  refine HasType.lam ?_
  refine HasType.all (HasType.lam ?_)
  refine HasType.all (HasType.lam ?_)
  refine HasType.imp ?_ (HasType.mkEq (α := .var primTyVar) htBvar1 htBvar0)
  exact HasType.mkEq (α := .var primTyVarB)
    (HasType.app (α := .var primTyVar) htBvar2 htBvar1)
    (HasType.app (α := .var primTyVar) htBvar2 htBvar0)

theorem HasType.ontoDef [Env.HasConnectives env] :
    HasType env [] Tm.ontoDef ontoTy := by
  unfold Tm.ontoDef ontoTy
  refine HasType.lam ?_
  refine HasType.all (HasType.lam ?_)
  refine HasType.ex (HasType.lam ?_)
  exact HasType.mkEq (α := .var primTyVarB) htBvar1
    (HasType.app (α := .var primTyVar) htBvar2 htBvar0)

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
    {f : ZFSet} (hf : f ∈ (.bool ↝ .bool ↝ .bool).denote ρ) :
    zfApp
        ((Tm.lam (.bool ↝ .bool ↝ .bool)
          (.app (.app (.bvar 0) (p.shift 1 0)) (q.shift 1 0))).denote
          M.interp ξ vs.vals)
        f =
      zfApp (zfApp f (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
  have h := HasType.denote_lam_app
    (HasType.app (HasType.app
        (HasType.bvar (Γ := (.bool ↝ .bool ↝ .bool) :: Γ)
          (α := .bool ↝ .bool ↝ .bool) (i := 0) List.getElem?_cons_zero)
        (hp.shift0 (.bool ↝ .bool ↝ .bool)))
      (hq.shift0 (.bool ↝ .bool ↝ .bool))) M.interp ξ vs hf
  simp only [HasType.denote, Tm.denote, CtxVal.cons] at h
  rw [Tm.denote_shift1_cons p, Tm.denote_shift1_cons q] at h
  exact h

theorem EnvModel.andExpand_app_right [Env.HasConnectives env]
    {Γ} (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ)
    {f : ZFSet} (hf : f ∈ (.bool ↝ .bool ↝ .bool).denote ρ) :
    zfApp
        ((Tm.lam (.bool ↝ .bool ↝ .bool)
          (.app (.app (.bvar 0) (Tm.tru.shift 1 0)) (Tm.tru.shift 1 0))).denote
          M.interp ξ vs.vals)
        f =
      zfApp (zfApp f zfTrue) zfTrue := by
  have h := HasType.denote_lam_app
    (HasType.app (HasType.app
        (HasType.bvar (Γ := (.bool ↝ .bool ↝ .bool) :: Γ)
          (α := .bool ↝ .bool ↝ .bool) (i := 0) List.getElem?_cons_zero)
        (HasType.tru.shift0 (.bool ↝ .bool ↝ .bool)))
      (HasType.tru.shift0 (.bool ↝ .bool ↝ .bool))) M.interp ξ vs hf
  simp only [HasType.denote, Tm.denote, CtxVal.cons] at h
  rw [Tm.shift_of_LC0 Tm.tru_LC, Tm.denote_LC0 _ _ _ _ Tm.tru_LC,
    EnvModel.denote_tru M ξ []] at h
  exact h

theorem EnvModel.andExpand_true_iff [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.andExpand q).denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfTrue ∧
        q.denote M.interp ξ vs.vals = zfTrue := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have hleft : HasType env Γ
      (.lam (.bool ↝ .bool ↝ .bool)
        (.app (.app (.bvar 0) (p.shift 1 0)) (q.shift 1 0)))
      ((.bool ↝ .bool ↝ .bool) ↝ .bool) :=
    HasType.lam (HasType.app (HasType.app (HasType.bvar (by simp)) (hp.shift0 _))
      (hq.shift0 _))
  have hright : HasType env Γ
      (.lam (.bool ↝ .bool ↝ .bool)
        (.app (.app (.bvar 0) (Tm.tru.shift 1 0)) (Tm.tru.shift 1 0)))
      ((.bool ↝ .bool ↝ .bool) ↝ .bool) :=
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
    have hfst : zfFst zfBool zfBool ∈ (.bool ↝ .bool ↝ .bool).denote ρ :=
      zfFst_mem zfBool zfBool
    have hsnd : zfSnd zfBool zfBool ∈ (.bool ↝ .bool ↝ .bool).denote ρ :=
      zfSnd_mem zfBool zfBool
    have hpT : p.denote M.interp ξ vs.vals = zfTrue := by
      have hL := EnvModel.andExpand_app_left hp hq M ξ vs hfst
      have hR := EnvModel.andExpand_app_right (Γ := Γ) M ξ vs hfst
      have h :=
        (hL.symm.trans (congrArg (fun g => zfApp g (zfFst zfBool zfBool)) heq)).trans
          hR
      rw [zfFst_app hpB hqB, zfFst_app zfTrue_mem_zfBool zfTrue_mem_zfBool] at h
      exact h
    have hqT : q.denote M.interp ξ vs.vals = zfTrue := by
      have hL := EnvModel.andExpand_app_left hp hq M ξ vs hsnd
      have hR := EnvModel.andExpand_app_right (Γ := Γ) M ξ vs hsnd
      have h :=
        (hL.symm.trans (congrArg (fun g => zfApp g (zfSnd zfBool zfBool)) heq)).trans
          hR
      rw [zfSnd_app hpB hqB, zfSnd_app zfTrue_mem_zfBool zfTrue_mem_zfBool] at h
      exact h
    exact ⟨hpT, hqT⟩
  · intro ⟨hpT, hqT⟩
    apply zfIsFunc_ext hfL hfR
    intro f hf
    have hL := EnvModel.andExpand_app_left hp hq M ξ vs hf
    have hR := EnvModel.andExpand_app_right (Γ := Γ) M ξ vs hf
    rw [hpT, hqT] at hL
    exact hL.trans hR.symm

theorem EnvModel.denote_and_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const andName andTy).denote M.interp ξ vs =
      Tm.andDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.and_ax HasType.andConst
    HasType.andDef ξ

private theorem htAndDefInner [Env.HasConnectives env] {Γ} :
    HasType env (.bool :: Γ)
      (Tm.lam .bool (Tm.andExpand (Tm.bvar 1) (Tm.bvar 0))) (.bool ↝ .bool) :=
  HasType.lam (HasType.andExpand
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp))
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp)))

private theorem htAndExpandBvars [Env.HasConnectives env] {Γ} :
    HasType env (.bool :: .bool :: Γ)
      (Tm.andExpand (Tm.bvar 1) (Tm.bvar 0)) .bool :=
  HasType.andExpand
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp))
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp))

theorem EnvModel.denote_and [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.and q).denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfTrue ∧
        q.denote M.interp ξ vs.vals = zfTrue := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have hand := EnvModel.denote_and_const M ξ vs.vals
  simp [Tm.denote] at hand
  have happ1 := Tm.denote_of_lam_app (htAndDefInner (Γ := [])) M.interp ξ
    (CtxVal.nil ρ) hpB
  have happ2 := Tm.denote_of_lam_app (htAndExpandBvars (Γ := [])) M.interp ξ
    ((CtxVal.nil ρ).cons (α := .bool) (p.denote M.interp ξ vs.vals) hpB) hqB
  simp [CtxVal.nil, CtxVal.cons] at happ1 happ2
  have hval :
      zfApp (zfApp (Tm.andDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) =
        (Tm.andExpand (Tm.bvar 1) (Tm.bvar 0)).denote M.interp ξ
          [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] :=
    (congrArg (fun g => zfApp g (q.denote M.interp ξ vs.vals)) happ1).trans happ2
  have hterm : (p.and q).denote M.interp ξ vs.vals =
      zfApp (zfApp (Tm.andDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
    simp [Tm.and, Tm.denote, hand]
  have hiff :=
    EnvModel.andExpand_true_iff
      (htBvar1 (γ := .bool) (α := .bool) (Γ := []))
      (htBvar0 (α := .bool) (Γ := [.bool]))
      M ξ ((CtxVal.nil ρ).cons (α := .bool) (p.denote M.interp ξ vs.vals) hpB |>.cons
        (α := .bool) (q.denote M.interp ξ vs.vals) hqB)
  simp [Tm.denote] at hiff
  exact (hterm.trans hval) ▸ hiff

/-! ## `⇒` -/

theorem EnvModel.denote_imp_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const impName impTy).denote M.interp ξ vs =
      Tm.impDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.imp_ax HasType.impConst
    HasType.impDef ξ

private theorem htImpDefInner [Env.HasConnectives env] {Γ} :
    HasType env (.bool :: Γ)
      (Tm.lam .bool (Tm.impExpand (Tm.bvar 1) (Tm.bvar 0))) (.bool ↝ .bool) :=
  HasType.lam (HasType.impExpand
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp))
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp)))

private theorem htImpExpandBvars [Env.HasConnectives env] {Γ} :
    HasType env (.bool :: .bool :: Γ)
      (Tm.impExpand (Tm.bvar 1) (Tm.bvar 0)) .bool :=
  HasType.impExpand
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp))
    (HasType.bvar (Γ := [.bool, .bool] ++ Γ) (by simp))

theorem EnvModel.denote_imp [Env.HasConnectives env]
    {Γ p q} (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (p.imp q).denote M.interp ξ vs.vals = zfTrue ↔
      (p.denote M.interp ξ vs.vals = zfTrue →
        q.denote M.interp ξ vs.vals = zfTrue) := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hqB := hq.denote_bool_mem M.interp ξ vs
  have himp := EnvModel.denote_imp_const M ξ vs.vals
  simp [Tm.denote] at himp
  have happ1 := Tm.denote_of_lam_app (htImpDefInner (Γ := [])) M.interp ξ
    (CtxVal.nil ρ) hpB
  have happ2 := Tm.denote_of_lam_app (htImpExpandBvars (Γ := [])) M.interp ξ
    ((CtxVal.nil ρ).cons (α := .bool) (p.denote M.interp ξ vs.vals) hpB) hqB
  simp [CtxVal.nil, CtxVal.cons] at happ1 happ2
  have hval :
      zfApp (zfApp (Tm.impDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) =
        (Tm.impExpand (Tm.bvar 1) (Tm.bvar 0)).denote M.interp ξ
          [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] :=
    (congrArg (fun g => zfApp g (q.denote M.interp ξ vs.vals)) happ1).trans happ2
  have hterm : (p.imp q).denote M.interp ξ vs.vals =
      zfApp (zfApp (Tm.impDef.denote M.interp ξ [])
          (p.denote M.interp ξ vs.vals))
        (q.denote M.interp ξ vs.vals) := by
    simp [Tm.imp, Tm.denote, himp]
  have hp' : HasType env [.bool, .bool] (Tm.bvar 1) .bool :=
    htBvar1 (γ := .bool) (α := .bool) (Γ := [])
  have hq' : HasType env [.bool, .bool] (Tm.bvar 0) .bool :=
    htBvar0 (α := .bool) (Γ := [.bool])
  let vs' : CtxVal ρ [.bool, .bool] :=
    (CtxVal.nil ρ).cons (α := .bool) (p.denote M.interp ξ vs.vals) hpB |>.cons
      (α := .bool) (q.denote M.interp ξ vs.vals) hqB
  have hvs : vs'.vals =
      [q.denote M.interp ξ vs.vals, p.denote M.interp ξ vs.vals] := rfl
  have hiff :=
    Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ (HasType.and hp' hq') hp' vs'
  have hand := EnvModel.denote_and hp' hq' M ξ vs'
  have handB := (HasType.and hp' hq').denote_bool_mem M.interp ξ vs'
  rw [hvs] at hiff hand handB
  simp [Tm.denote] at hiff hand handB
  have hpq :
      (Tm.impExpand (Tm.bvar 1) (Tm.bvar 0)).denote M.interp ξ
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
          (Tm.imp (Tm.all α (.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (.bvar 1))))
            (.bvar 0)))) := by
  simp [Tm.exDef, Tm.all, Tm.imp, Tm.instTy, Ty.inst, TySubst.lookup, primTyVar,
    impTy]

theorem Tm.oneOneDef_instTy (α β : Ty) :
    Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)] =
      .lam (α ↝ β)
        (Tm.all α (.lam α
          (Tm.all α (.lam α
            (Tm.imp (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
              (Tm.mkEq α (.bvar 1) (.bvar 0))))))) := by
  simp [Tm.oneOneDef, Tm.all, Tm.imp, Tm.mkEq, Tm.eqConst, Tm.instTy, Ty.inst,
    TySubst.lookup, primTyVar, primTyVarB, impTy]

theorem Tm.ontoDef_instTy (α β : Ty) :
    Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)] =
      .lam (α ↝ β)
        (Tm.all β (.lam β
          (Tm.ex α (.lam α
            (Tm.mkEq β (.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0))))))) := by
  simp [Tm.ontoDef, Tm.all, Tm.ex, Tm.mkEq, Tm.eqConst, Tm.instTy, Ty.inst,
    TySubst.lookup, primTyVar, primTyVarB]

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
    simp [EnvModel.denote_lam_tru, zfConst_app hx] at this
    exact this
  · intro hall
    rw [EnvModel.denote_lam_tru]
    apply zfIsFunc_ext hPmem hTmem
    intro x hx
    simp [zfConst_app hx, hall x hx]

theorem EnvModel.denote_all_const [Env.HasConnectives env]
    (α : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const allName ((α ↝ .bool) ↝ .bool)).denote M.interp ξ vs =
      (Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0))).denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  have hunf :=
    EnvModel.unfold_poly M [(primTyVar, α)] Env.HasConnectives.all_ax
      (HasType.allConst (.var primTyVar)) HasType.allDef ξ
  simpa [Tm.allTy_inst, Tm.allDef_instTy] using hunf

private theorem htAllExpandBvar [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env ((α ↝ .bool) :: Γ) (Tm.allExpand α (Tm.bvar 0)) .bool :=
  HasType.allExpand (HasType.bvar (Γ := (α ↝ .bool) :: Γ) (by simp))

theorem EnvModel.denote_all [Env.HasConnectives env]
    {Γ α P} (hP : HasType env Γ P (α ↝ .bool))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.all α P).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ x ∈ α.denote ρ, zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
  have hPmem := hP.denote_mem M.interp ξ vs
  have hPset : P.denote M.interp ξ vs.vals ∈ (α ↝ .bool).denote ρ := by
    simpa [HasType.denote, Ty.denote_arrow] using hPmem
  have hconst := EnvModel.denote_all_const α M ξ vs.vals
  simp [Tm.denote] at hconst
  have happ := Tm.denote_of_lam_app (htAllExpandBvar (α := α) (Γ := []))
    M.interp ξ (CtxVal.nil ρ) hPset
  have hterm : (Tm.all α P).denote M.interp ξ vs.vals =
      zfApp ((Tm.lam (α ↝ .bool) (Tm.allExpand α (Tm.bvar 0))).denote
          M.interp ξ [])
        (P.denote M.interp ξ vs.vals) := by
    simp [Tm.all, Tm.denote, hconst]
  have hP' : HasType env [α ↝ .bool] (Tm.bvar 0) (α ↝ .bool) :=
    HasType.bvar (by simp)
  let vs' : CtxVal ρ [α ↝ .bool] :=
    (CtxVal.nil ρ).cons (P.denote M.interp ξ vs.vals) hPset
  have hvs : vs'.vals = [P.denote M.interp ξ vs.vals] := rfl
  have hiff := EnvModel.allExpand_true_iff hP' M ξ vs'
  rw [hvs] at hiff
  simp [Tm.denote] at hiff
  exact (hterm.trans (by simpa [CtxVal.nil] using happ)) ▸ hiff

/-! ## `⊥` and `¬` -/

private theorem htIdBool [Env.HasConnectives env] {Γ} :
    HasType env Γ (Tm.lam .bool (Tm.bvar 0)) (.bool ↝ .bool) :=
  HasType.lam (HasType.bvar (by simp))

private theorem htBvar0Bool [Env.HasConnectives env] {Γ} :
    HasType env (.bool :: Γ) (Tm.bvar 0) .bool :=
  HasType.bvar (by simp)

theorem EnvModel.denote_falsum [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    Tm.falsum.denote M.interp ξ vs = zfFalse := by
  rw [Tm.denote_LC0 _ _ _ _ Tm.falsum_LC]
  have hunf :=
    EnvModel.unfold_mono M Env.HasConnectives.falsum_ax HasType.falsum
      HasType.falsumDef ξ
  have hiff := EnvModel.denote_all (htIdBool (Γ := [])) M ξ (CtxVal.nil ρ)
  have hF : zfApp ((Tm.lam .bool (Tm.bvar 0)).denote M.interp ξ []) zfFalse =
      zfFalse :=
    Tm.denote_of_lam_app (htBvar0Bool (Γ := [])) M.interp ξ (CtxVal.nil ρ)
      zfFalse_mem_zfBool
  have hne : (Tm.all .bool (Tm.lam .bool (Tm.bvar 0))).denote M.interp ξ [] ≠
      zfTrue := by
    intro hT
    exact zfFalse_ne_zfTrue (hF ▸ (hiff.1 hT) zfFalse zfFalse_mem_zfBool)
  have hB := HasType.falsumDef.denote_bool_mem M.interp ξ (CtxVal.nil ρ)
  simp [CtxVal.nil, Tm.falsumDef] at hB
  have : (Tm.all .bool (Tm.lam .bool (Tm.bvar 0))).denote M.interp ξ [] =
      zfFalse :=
    zfBool_eq_false_of_ne_true hB hne
  exact hunf.trans this

theorem EnvModel.denote_not_const [Env.HasConnectives env]
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) :
    (Tm.const notName notTy).denote M.interp ξ vs =
      Tm.notDef.denote M.interp ξ [] := by
  rw [Tm.denote_LC0 _ _ _ _ (by rfl)]
  exact EnvModel.unfold_mono M Env.HasConnectives.not_ax HasType.notConst
    HasType.notDef ξ

private theorem htNotBody [Env.HasConnectives env] {Γ} :
    HasType env (.bool :: Γ) (Tm.imp (Tm.bvar 0) Tm.falsum) .bool :=
  HasType.imp (HasType.bvar (by simp)) HasType.falsum

theorem EnvModel.denote_not [Env.HasConnectives env]
    {Γ p} (hp : HasType env Γ p .bool)
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    p.not.denote M.interp ξ vs.vals = zfTrue ↔
      p.denote M.interp ξ vs.vals = zfFalse := by
  have hpB := hp.denote_bool_mem M.interp ξ vs
  have hconst := EnvModel.denote_not_const M ξ vs.vals
  simp [Tm.denote] at hconst
  have happ := Tm.denote_of_lam_app (htNotBody (Γ := [])) M.interp ξ
    (CtxVal.nil ρ) hpB
  have hterm : p.not.denote M.interp ξ vs.vals =
      zfApp (Tm.notDef.denote M.interp ξ []) (p.denote M.interp ξ vs.vals) := by
    simp [Tm.not, Tm.denote, hconst]
  have hval :
      zfApp (Tm.notDef.denote M.interp ξ []) (p.denote M.interp ξ vs.vals) =
        (Tm.imp (Tm.bvar 0) Tm.falsum).denote M.interp ξ
          [p.denote M.interp ξ vs.vals] := by
    simpa [Tm.notDef, CtxVal.nil] using happ
  have hp' : HasType env [.bool] (Tm.bvar 0) .bool :=
    htBvar0 (α := .bool) (Γ := [])
  let vs' : CtxVal ρ [.bool] :=
    (CtxVal.nil ρ).cons (α := .bool) (p.denote M.interp ξ vs.vals) hpB
  have hvs : vs'.vals = [p.denote M.interp ξ vs.vals] := rfl
  have hiff := EnvModel.denote_imp hp' HasType.falsum M ξ vs'
  rw [hvs] at hiff
  simp [Tm.denote, EnvModel.denote_falsum] at hiff
  have hneq : (p.denote M.interp ξ vs.vals = zfTrue → zfFalse = zfTrue) ↔
      p.denote M.interp ξ vs.vals = zfFalse := by
    constructor
    · intro himp
      exact zfBool_eq_false_of_ne_true hpB fun hpT => zfFalse_ne_zfTrue (himp hpT)
    · intro hpF hpT
      exact (zfFalse_ne_zfTrue (hpF ▸ hpT)).elim
  exact (hterm.trans hval) ▸ (hiff.trans hneq)

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

/-- `P x` under binders `x, q, P`. -/
private theorem htExPx [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env (α :: .bool :: (α ↝ .bool) :: Γ)
      (Tm.app (Tm.bvar 2) (Tm.bvar 0)) .bool :=
  HasType.app (α := α)
    (HasType.bvar (Γ := α :: .bool :: (α ↝ .bool) :: Γ) (by simp))
    (HasType.bvar (by simp))

private theorem htExImpX [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env (α :: .bool :: (α ↝ .bool) :: Γ)
      (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1)) .bool :=
  HasType.imp (htExPx (α := α)) (HasType.bvar (by simp))

private theorem htExLamX [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env (.bool :: (α ↝ .bool) :: Γ)
      (Tm.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1)))
      (α ↝ .bool) :=
  HasType.lam (htExImpX (α := α))

private theorem htExAllX [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env (.bool :: (α ↝ .bool) :: Γ)
      (Tm.all α (Tm.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))))
      .bool :=
  HasType.all (htExLamX (α := α))

private theorem htExImpQ [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env (.bool :: (α ↝ .bool) :: Γ)
      (Tm.imp
        (Tm.all α (Tm.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))))
        (Tm.bvar 0)) .bool :=
  HasType.imp (htExAllX (α := α)) (HasType.bvar (by simp))

private theorem htExLamQ [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env ((α ↝ .bool) :: Γ)
      (Tm.lam .bool
        (Tm.imp
          (Tm.all α (Tm.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))))
          (Tm.bvar 0)))
      (.bool ↝ .bool) :=
  HasType.lam (htExImpQ (α := α))

private theorem htExBody [Env.HasConnectives env] {α : Ty} {Γ} :
    HasType env ((α ↝ .bool) :: Γ)
      (Tm.all .bool (.lam .bool
        (Tm.imp
          (Tm.all α (.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))))
          (Tm.bvar 0)))) .bool :=
  HasType.all (htExLamQ (α := α))

/-- `P x ⇒ q` at values `x, q, P`. -/
theorem EnvModel.denote_ex_imp_x [Env.HasConnectives env]
    (α : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {P q x : ZFSet}
    (hP : P ∈ (α ↝ .bool).denote ρ) (hq : q ∈ zfBool) (hx : x ∈ α.denote ρ) :
    zfApp
        ((Tm.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))).denote
          M.interp ξ [q, P])
        x = zfTrue ↔
      (zfApp P x = zfTrue → q = zfTrue) := by
  let vsP : CtxVal ρ [α ↝ .bool] := (CtxVal.nil ρ).cons P hP
  let vsq : CtxVal ρ [.bool, α ↝ .bool] := vsP.cons (α := .bool) q hq
  let vsx : CtxVal ρ [α, .bool, α ↝ .bool] := vsq.cons (α := α) x hx
  have happx := Tm.denote_of_lam_app (htExImpX (α := α) (Γ := []))
    M.interp ξ vsq hx
  have himpx := EnvModel.denote_imp (htExPx (α := α) (Γ := []))
    (htBvar1 (γ := α) (α := .bool) (Γ := [α ↝ .bool])) M ξ vsx
  have hvsx : vsx.vals = [x, q, P] := rfl
  have hvsq : vsq.vals = [q, P] := rfl
  rw [hvsx] at himpx
  rw [hvsq] at happx
  simp [Tm.denote] at himpx
  exact happx.symm ▸ himpx

/-- `(∀ x. P x ⇒ q) ⇒ q` at values `q, P`. -/
theorem EnvModel.denote_ex_imp_q [Env.HasConnectives env]
    (α : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {P q : ZFSet}
    (hP : P ∈ (α ↝ .bool).denote ρ) (hq : q ∈ zfBool) :
    zfApp
        ((Tm.lam .bool
          (Tm.imp
            (Tm.all α (Tm.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))))
            (Tm.bvar 0))).denote M.interp ξ [P])
        q = zfTrue ↔
      ((∀ x ∈ α.denote ρ, zfApp P x = zfTrue → q = zfTrue) → q = zfTrue) := by
  let vsP : CtxVal ρ [α ↝ .bool] := (CtxVal.nil ρ).cons P hP
  let vsq : CtxVal ρ [.bool, α ↝ .bool] := vsP.cons (α := .bool) q hq
  have happq := Tm.denote_of_lam_app (htExImpQ (α := α) (Γ := []))
    M.interp ξ vsP hq
  have hallx := EnvModel.denote_all (htExLamX (α := α) (Γ := [])) M ξ vsq
  have himp := EnvModel.denote_imp (htExAllX (α := α) (Γ := []))
    (htBvar0 (α := .bool) (Γ := [α ↝ .bool])) M ξ vsq
  have hvsP : vsP.vals = [P] := rfl
  have hvsq : vsq.vals = [q, P] := rfl
  rw [hvsP] at happq
  rw [hvsq] at hallx himp
  simp [Tm.denote] at himp
  constructor
  · intro happT hallq
    refine himp.1 (happq ▸ happT) ?_
    refine hallx.2 ?_
    intro x hx
    exact (EnvModel.denote_ex_imp_x α M ξ hP hq hx).2 (hallq x hx)
  · intro himpq
    exact happq.symm ▸ himp.2 fun hallT =>
      himpq fun x hx => (EnvModel.denote_ex_imp_x α M ξ hP hq hx).1 (hallx.1 hallT x hx)

theorem EnvModel.denote_ex [Env.HasConnectives env]
    {Γ α P} (hP : HasType env Γ P (α ↝ .bool))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.ex α P).denote M.interp ξ vs.vals = zfTrue ↔
      ∃ x ∈ α.denote ρ, zfApp (P.denote M.interp ξ vs.vals) x = zfTrue := by
  have hPset : P.denote M.interp ξ vs.vals ∈ (α ↝ .bool).denote ρ := by
    simpa [HasType.denote, Ty.denote_arrow] using hP.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_ex_const α M ξ vs.vals
  simp [Tm.denote] at hconst
  have happ := Tm.denote_of_lam_app (htExBody (α := α) (Γ := []))
    M.interp ξ (CtxVal.nil ρ) hPset
  have hval :
      zfApp ((Tm.exDef.instTy [(primTyVar, α)]).denote M.interp ξ [])
          (P.denote M.interp ξ vs.vals) =
        (Tm.all .bool (.lam .bool
          (Tm.imp (Tm.all α (.lam α (Tm.imp (Tm.app (Tm.bvar 2) (Tm.bvar 0)) (Tm.bvar 1))))
            (Tm.bvar 0)))).denote M.interp ξ
          [P.denote M.interp ξ vs.vals] := by
    simpa [Tm.exDef_instTy, CtxVal.nil] using happ
  have hterm : (Tm.ex α P).denote M.interp ξ vs.vals =
      zfApp ((Tm.exDef.instTy [(primTyVar, α)]).denote M.interp ξ [])
        (P.denote M.interp ξ vs.vals) := by
    simp [Tm.ex, Tm.denote, hconst]
  let vsP : CtxVal ρ [α ↝ .bool] :=
    (CtxVal.nil ρ).cons (P.denote M.interp ξ vs.vals) hPset
  have hall := EnvModel.denote_all (htExLamQ (α := α) (Γ := [])) M ξ vsP
  have hvsP : vsP.vals = [P.denote M.interp ξ vs.vals] := rfl
  rw [hvsP] at hall
  refine (hterm.trans hval) ▸ hall.trans ?_
  refine Iff.trans (forall_congr' fun q => forall_congr' fun hq =>
    EnvModel.denote_ex_imp_q α M ξ hPset hq) zfBool_exists_iff

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

private theorem htOOFx [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: α :: (α ↝ β) :: Γ)
      (Tm.app (Tm.bvar 2) (Tm.bvar 1)) β :=
  HasType.app (α := α)
    (HasType.bvar (Γ := α :: α :: (α ↝ β) :: Γ) (by simp))
    (HasType.bvar (by simp))

private theorem htOOFy [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: α :: (α ↝ β) :: Γ)
      (Tm.app (Tm.bvar 2) (Tm.bvar 0)) β :=
  HasType.app (α := α)
    (HasType.bvar (Γ := α :: α :: (α ↝ β) :: Γ) (by simp))
    (HasType.bvar (by simp))

private theorem htOOEqF [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: α :: (α ↝ β) :: Γ)
      (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
      .bool :=
  HasType.mkEq (α := β) (htOOFx (α := α) (β := β)) (htOOFy (α := α) (β := β))

private theorem htOOEqXY [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: α :: (α ↝ β) :: Γ)
      (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0)) .bool :=
  HasType.mkEq (α := α)
    (HasType.bvar (Γ := α :: α :: (α ↝ β) :: Γ) (by simp))
    (HasType.bvar (by simp))

private theorem htOOImp [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: α :: (α ↝ β) :: Γ)
      (Tm.imp
        (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
        (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0))) .bool :=
  HasType.imp (htOOEqF (α := α) (β := β)) (htOOEqXY (α := α) (β := β))

private theorem htOOLamY [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: (α ↝ β) :: Γ)
      (Tm.lam α
        (Tm.imp
          (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
          (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0))))
      (α ↝ .bool) :=
  HasType.lam (htOOImp (α := α) (β := β))

private theorem htOOAllY [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: (α ↝ β) :: Γ)
      (Tm.all α
        (Tm.lam α
          (Tm.imp
            (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
            (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0))))) .bool :=
  HasType.all (htOOLamY (α := α) (β := β))

private theorem htOOLamX [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env ((α ↝ β) :: Γ)
      (Tm.lam α
        (Tm.all α
          (Tm.lam α
            (Tm.imp
              (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
              (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0))))))
      (α ↝ .bool) :=
  HasType.lam (htOOAllY (α := α) (β := β))

private theorem htOOBody [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env ((α ↝ β) :: Γ)
      (Tm.all α
        (Tm.lam α
          (Tm.all α
            (Tm.lam α
              (Tm.imp
                (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1))
                  (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
                (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0))))))) .bool :=
  HasType.all (htOOLamX (α := α) (β := β))

theorem EnvModel.denote_oneOne_imp [Env.HasConnectives env]
    (α β : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {f x y : ZFSet}
    (hf : f ∈ (α ↝ β).denote ρ) (hx : x ∈ α.denote ρ) (hy : y ∈ α.denote ρ) :
    zfApp
        ((Tm.lam α
          (Tm.imp
            (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1))
              (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
            (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0)))).denote
          M.interp ξ [x, f])
        y = zfTrue ↔
      (zfApp f x = zfApp f y → x = y) := by
  let vsf : CtxVal ρ [α ↝ β] := (CtxVal.nil ρ).cons f hf
  let vsx : CtxVal ρ [α, α ↝ β] := vsf.cons (α := α) x hx
  let vsy : CtxVal ρ [α, α, α ↝ β] := vsx.cons (α := α) y hy
  have happy := Tm.denote_of_lam_app (htOOImp (α := α) (β := β) (Γ := []))
    M.interp ξ vsx hy
  have himp := EnvModel.denote_imp (htOOEqF (α := α) (β := β) (Γ := []))
    (htOOEqXY (α := α) (β := β) (Γ := [])) M ξ vsy
  have heqL := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
    (htOOFx (α := α) (β := β) (Γ := [])) (htOOFy (α := α) (β := β) (Γ := [])) vsy
  have heqR := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
    (htBvar1 (γ := α) (α := α) (Γ := [α ↝ β]))
    (htBvar0 (α := α) (Γ := [α, α ↝ β])) vsy
  have hvsx : vsx.vals = [x, f] := rfl
  have hvsy : vsy.vals = [y, x, f] := rfl
  rw [hvsx] at happy
  rw [hvsy] at himp heqL heqR
  simp [Tm.denote] at himp heqL heqR
  exact happy.symm ▸ himp.trans (Iff.imp heqL heqR)

theorem EnvModel.denote_oneOne_at [Env.HasConnectives env]
    (α β : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {f x : ZFSet}
    (hf : f ∈ (α ↝ β).denote ρ) (hx : x ∈ α.denote ρ) :
    zfApp
        ((Tm.lam α
          (Tm.all α
            (Tm.lam α
              (Tm.imp
                (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1))
                  (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
                (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0)))))).denote
          M.interp ξ [f])
        x = zfTrue ↔
      ∀ y ∈ α.denote ρ, zfApp f x = zfApp f y → x = y := by
  let vsf : CtxVal ρ [α ↝ β] := (CtxVal.nil ρ).cons f hf
  let vsx : CtxVal ρ [α, α ↝ β] := vsf.cons (α := α) x hx
  have happx := Tm.denote_of_lam_app (htOOAllY (α := α) (β := β) (Γ := []))
    M.interp ξ vsf hx
  have hally := EnvModel.denote_all (htOOLamY (α := α) (β := β) (Γ := [])) M ξ vsx
  have hvsf : vsf.vals = [f] := rfl
  have hvsx : vsx.vals = [x, f] := rfl
  rw [hvsf] at happx
  rw [hvsx] at hally
  refine happx.symm ▸ hally.trans ?_
  exact forall_congr' fun y => forall_congr' fun hy =>
    EnvModel.denote_oneOne_imp α β M ξ hf hx hy

theorem EnvModel.denote_oneOne [Env.HasConnectives env]
    {Γ α β f} (hf : HasType env Γ f (α ↝ β))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.oneOne α β f).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ x ∈ α.denote ρ, ∀ y ∈ α.denote ρ,
        zfApp (f.denote M.interp ξ vs.vals) x =
          zfApp (f.denote M.interp ξ vs.vals) y → x = y := by
  have hfset : f.denote M.interp ξ vs.vals ∈ (α ↝ β).denote ρ := by
    simpa [HasType.denote, Ty.denote_arrow] using hf.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_oneOne_const α β M ξ vs.vals
  simp [Tm.denote] at hconst
  have happ := Tm.denote_of_lam_app (htOOBody (α := α) (β := β) (Γ := []))
    M.interp ξ (CtxVal.nil ρ) hfset
  have hval :
      zfApp ((Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) =
      (Tm.all α (.lam α
        (Tm.all α (.lam α
          (Tm.imp (Tm.mkEq β (Tm.app (Tm.bvar 2) (Tm.bvar 1)) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))
            (Tm.mkEq α (Tm.bvar 1) (Tm.bvar 0))))))).denote M.interp ξ
        [f.denote M.interp ξ vs.vals] := by
    simpa [Tm.oneOneDef_instTy, CtxVal.nil] using happ
  have hterm : (Tm.oneOne α β f).denote M.interp ξ vs.vals =
      zfApp ((Tm.oneOneDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) := by
    simp [Tm.oneOne, Tm.denote, hconst]
  let vsf : CtxVal ρ [α ↝ β] :=
    (CtxVal.nil ρ).cons (f.denote M.interp ξ vs.vals) hfset
  have hallx := EnvModel.denote_all (htOOLamX (α := α) (β := β) (Γ := [])) M ξ vsf
  have hvsf : vsf.vals = [f.denote M.interp ξ vs.vals] := rfl
  rw [hvsf] at hallx
  refine (hterm.trans hval) ▸ hallx.trans ?_
  exact forall_congr' fun x => forall_congr' fun hx =>
    EnvModel.denote_oneOne_at α β M ξ hfset hx

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

private theorem htOntoFx [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: β :: (α ↝ β) :: Γ)
      (Tm.app (Tm.bvar 2) (Tm.bvar 0)) β :=
  HasType.app (α := α)
    (HasType.bvar (Γ := α :: β :: (α ↝ β) :: Γ) (by simp))
    (HasType.bvar (by simp))

private theorem htOntoEq [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (α :: β :: (α ↝ β) :: Γ)
      (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0))) .bool :=
  HasType.mkEq (α := β)
    (HasType.bvar (Γ := α :: β :: (α ↝ β) :: Γ) (by simp))
    (htOntoFx (α := α) (β := β))

private theorem htOntoLamX [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (β :: (α ↝ β) :: Γ)
      (Tm.lam α (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0))))
      (α ↝ .bool) :=
  HasType.lam (htOntoEq (α := α) (β := β))

private theorem htOntoEx [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env (β :: (α ↝ β) :: Γ)
      (Tm.ex α (Tm.lam α (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))))
      .bool :=
  HasType.ex (htOntoLamX (α := α) (β := β))

private theorem htOntoLamY [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env ((α ↝ β) :: Γ)
      (Tm.lam β (Tm.ex α (Tm.lam α (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0))))))
      (β ↝ .bool) :=
  HasType.lam (htOntoEx (α := α) (β := β))

private theorem htOntoBody [Env.HasConnectives env] {α β : Ty} {Γ} :
    HasType env ((α ↝ β) :: Γ)
      (Tm.all β
        (Tm.lam β (Tm.ex α (Tm.lam α
          (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0))))))) .bool :=
  HasType.all (htOntoLamY (α := α) (β := β))

theorem EnvModel.denote_onto_eq [Env.HasConnectives env]
    (α β : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {f y x : ZFSet}
    (hf : f ∈ (α ↝ β).denote ρ) (hy : y ∈ β.denote ρ) (hx : x ∈ α.denote ρ) :
    zfApp
        ((Tm.lam α (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))).denote
          M.interp ξ [y, f])
        x = zfTrue ↔
      y = zfApp f x := by
  let vsf : CtxVal ρ [α ↝ β] := (CtxVal.nil ρ).cons f hf
  let vsy : CtxVal ρ [β, α ↝ β] := vsf.cons (α := β) y hy
  let vsx : CtxVal ρ [α, β, α ↝ β] := vsy.cons (α := α) x hx
  have happx := Tm.denote_of_lam_app (htOntoEq (α := α) (β := β) (Γ := []))
    M.interp ξ vsy hx
  have heq := Tm.denote_mkEq_true_iff M.interp M.eq_ok ξ
    (htBvar1 (γ := α) (α := β) (Γ := [α ↝ β]))
    (htOntoFx (α := α) (β := β) (Γ := [])) vsx
  have hvsy : vsy.vals = [y, f] := rfl
  have hvsx : vsx.vals = [x, y, f] := rfl
  rw [hvsy] at happx
  rw [hvsx] at heq
  simp [Tm.denote] at heq
  exact happx.symm ▸ heq

theorem EnvModel.denote_onto_at [Env.HasConnectives env]
    (α β : Ty) (M : EnvModel env ρ) (ξ : FVarVal ρ)
    {f y : ZFSet}
    (hf : f ∈ (α ↝ β).denote ρ) (hy : y ∈ β.denote ρ) :
    zfApp
        ((Tm.lam β
          (Tm.ex α (Tm.lam α
            (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0)))))).denote
          M.interp ξ [f])
        y = zfTrue ↔
      ∃ x ∈ α.denote ρ, y = zfApp f x := by
  let vsf : CtxVal ρ [α ↝ β] := (CtxVal.nil ρ).cons f hf
  let vsy : CtxVal ρ [β, α ↝ β] := vsf.cons (α := β) y hy
  have happy := Tm.denote_of_lam_app (htOntoEx (α := α) (β := β) (Γ := []))
    M.interp ξ vsf hy
  have hex := EnvModel.denote_ex (htOntoLamX (α := α) (β := β) (Γ := [])) M ξ vsy
  have hvsf : vsf.vals = [f] := rfl
  have hvsy : vsy.vals = [y, f] := rfl
  rw [hvsf] at happy
  rw [hvsy] at hex
  refine happy.symm ▸ hex.trans ?_
  exact exists_congr fun x => and_congr_right fun hx =>
    EnvModel.denote_onto_eq α β M ξ hf hy hx

theorem EnvModel.denote_onto [Env.HasConnectives env]
    {Γ α β f} (hf : HasType env Γ f (α ↝ β))
    (M : EnvModel env ρ) (ξ : FVarVal ρ) (vs : CtxVal ρ Γ) :
    (Tm.onto α β f).denote M.interp ξ vs.vals = zfTrue ↔
      ∀ y ∈ β.denote ρ, ∃ x ∈ α.denote ρ,
        y = zfApp (f.denote M.interp ξ vs.vals) x := by
  have hfset : f.denote M.interp ξ vs.vals ∈ (α ↝ β).denote ρ := by
    simpa [HasType.denote, Ty.denote_arrow] using hf.denote_mem M.interp ξ vs
  have hconst := EnvModel.denote_onto_const α β M ξ vs.vals
  simp [Tm.denote] at hconst
  have happ := Tm.denote_of_lam_app (htOntoBody (α := α) (β := β) (Γ := []))
    M.interp ξ (CtxVal.nil ρ) hfset
  have hval :
      zfApp ((Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) =
      (Tm.all β (.lam β
        (Tm.ex α (.lam α (Tm.mkEq β (Tm.bvar 1) (Tm.app (Tm.bvar 2) (Tm.bvar 0))))))).denote
        M.interp ξ [f.denote M.interp ξ vs.vals] := by
    simpa [Tm.ontoDef_instTy, CtxVal.nil] using happ
  have hterm : (Tm.onto α β f).denote M.interp ξ vs.vals =
      zfApp ((Tm.ontoDef.instTy [(primTyVar, α), (primTyVarB, β)]).denote
          M.interp ξ [])
        (f.denote M.interp ξ vs.vals) := by
    simp [Tm.onto, Tm.denote, hconst]
  let vsf : CtxVal ρ [α ↝ β] :=
    (CtxVal.nil ρ).cons (f.denote M.interp ξ vs.vals) hfset
  have hally := EnvModel.denote_all (htOntoLamY (α := α) (β := β) (Γ := [])) M ξ vsf
  have hvsf : vsf.vals = [f.denote M.interp ξ vs.vals] := rfl
  rw [hvsf] at hally
  refine (hterm.trans hval) ▸ hally.trans ?_
  exact forall_congr' fun y => forall_congr' fun hy =>
    EnvModel.denote_onto_at α β M ξ hfset hy

end HOLean
