/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Model.Sound
import HOLean.Connective

/-!
# Models of definitional extensions

If `I` models `env` and `rhs` is a closed term of generic type `ty`
whose schematic variables are those of `ty`, then interpreting the new
constant at each instance by `⟦rhs[θ]⟧` models `env.addDef n ty rhs`.
-/

open ZFSet Classical

namespace HOLean

variable {env : Env} {ρ : TyVal}

/-- Interpret a defined constant at an instance of its generic type. -/
noncomputable def interpDef (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (ty : Ty) (rhs : Tm) (inst : Ty) : ZFSet :=
  match ty.matchTy inst [] with
  | some θ => (rhs.instTy θ).denote I ξ []
  | none => ∅

theorem interpDef_mem (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    {ty : Ty} {rhs : Tm} {inst : Ty}
    (hrhs : HasType env [] rhs ty) (hinst : ty.isInstanceOf inst) :
    interpDef I ξ ty rhs inst ∈ inst.denote ρ := by
  have hsome := Ty.matchTy_of_isInstanceOf hinst
  simp [interpDef]
  cases hθ : ty.matchTy inst [] with
  | none =>
    simp [hθ] at hsome
  | some θ =>
    have hty : ty.inst θ = inst := Ty.matchTy_sound hθ
    have htyped : HasType env [] (rhs.instTy θ) (ty.inst θ) := hrhs.instTy θ
    simpa [hty, HasType.denote, CtxVal.nil] using
      htyped.denote_mem I ξ (CtxVal.nil ρ)

/-- Extend an environment interpretation by a definition. -/
noncomputable def EnvInterp.addDef {n : Name} {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) :
    EnvInterp (env.addDef n ty rhs) ρ where
  interp m inst :=
    if m = n then interpDef I ξ ty rhs inst else I.interp m inst
  mem := by
    intro m inst gen hconst hinst
    by_cases hm : m = n
    · subst hm
      have hty : gen = ty := by
        have h := hconst
        simp [Env.addDef_constants_self] at h
        exact h.symm
      subst hty
      simpa using interpDef_mem I ξ hrhs hinst
    · have hconst' : env.constants m = some gen := by
        rwa [Env.addDef_constants_of_ne env ty rhs hm] at hconst
      simpa [hm] using I.mem hconst' hinst

@[simp] theorem EnvInterp.addDef_interp_self (n : Name) {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (inst : Ty) :
    (I.addDef (n := n) ξ hrhs).interp n inst = interpDef I ξ ty rhs inst := by
  simp [EnvInterp.addDef]

theorem EnvInterp.addDef_interp_of_ne (n : Name) {m : Name} {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (hne : m ≠ n) (inst : Ty) :
    (I.addDef (n := n) ξ hrhs).interp m inst = I.interp m inst := by
  simp [EnvInterp.addDef, hne]

/-- Substitutions produced by matching `ty` against `ty.inst θ` agree with
`θ` on every type variable of `ty`. -/
theorem matchTy_inst_agrees (ty : Ty) (θ : TySubst) :
    ∃ σ, ty.matchTy (ty.inst θ) [] = some σ ∧ Ty.agrees σ θ :=
  Ty.matchTy_complete (Ty.agrees_nil θ)

theorem instTy_eq_of_match {rhs : Tm} {ty : Ty} {θ σ : TySubst}
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    (hm : ty.matchTy (ty.inst θ) [] = some σ)
    (hag : Ty.agrees σ θ) :
    rhs.instTy σ = rhs.instTy θ := by
  apply Tm.instTy_eq_of
  intro x hx
  have hx' : x ∈ ty.tyvars := hvars x hx
  have hsome : (σ.lookup x).isSome = true := (Ty.matchTy_spec hm).2.1 x hx'
  cases hlook : σ.lookup x with
  | none =>
    simp [hlook] at hsome
  | some α =>
    have := hag x α hlook
    simp [this]

theorem EnvInterp.addDef_eq_ok [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (hne_eq : n ≠ eqName)
    (heq : ∀ α, I.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ))
    (α : Ty) :
    (I.addDef (n := n) ξ hrhs).interp eqName (α ↝ α ↝ .bool) =
      zfEq (α.denote ρ) := by
  rw [EnvInterp.addDef_interp_of_ne n I ξ hrhs hne_eq.symm]
  exact heq α

theorem EnvInterp.addDef_inst_of_ne (n : Name) {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (θ : TySubst) {m : Name}
    (hm : m ≠ n) (α : Ty) :
    ((I.addDef (n := n) ξ hrhs).inst θ).interp m α = (I.inst θ).interp m α := by
  simp [EnvInterp.inst, EnvInterp.addDef_interp_of_ne n I ξ hrhs hm]

/-- Transport a model along `addDef`.  The right-hand side must be a closed
term whose schematic variables are among those of the generic type, and
the new name must be fresh (so old axioms do not mention it). -/
noncomputable def EnvModel.addDef [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hn : env.constants n = none) (hne_eq : n ≠ eqName)
    (hwf : env.WF) (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars) :
    EnvModel (env.addDef n ty rhs) ρ where
  interp := M.interp.addDef (n := n) (FVarVal.ofNonempty hρ) hrhs
  eq_ok :=
    EnvInterp.addDef_eq_ok n M.interp (FVarVal.ofNonempty hρ) hrhs hne_eq M.eq_ok
  ax_ok := fun θ p hp ξ => by
    have : Env.HasEq (env.addDef n ty rhs) := Env.HasEq.addDef hne_eq
    match hp with
    | Or.inl heq =>
      subst heq
      set ξ0 := FVarVal.ofNonempty hρ
      set I' := M.interp.addDef (n := n) ξ0 hrhs
      have hrhs_fresh : rhs.hasConst n = false :=
        hrhs.not_hasConst_of_fresh hn
      have hconst_eq :
          (Tm.const n ty).denote (I'.inst θ) ξ [] =
            interpDef M.interp ξ0 ty rhs (ty.inst θ) := by
        simp [Tm.denote, EnvInterp.inst]
        exact EnvInterp.addDef_interp_self n M.interp ξ0 hrhs (ty.inst θ)
      obtain ⟨σ, hσ, hag⟩ := matchTy_inst_agrees ty θ
      have hinterp :
          interpDef M.interp ξ0 ty rhs (ty.inst θ) =
            (rhs.instTy σ).denote M.interp ξ0 [] := by
        simp [interpDef, hσ]
      have hinstTy : rhs.instTy σ = rhs.instTy θ :=
        instTy_eq_of_match hvars hσ hag
      have hrhs_den :
          rhs.denote (I'.inst θ) ξ [] =
            (rhs.instTy θ).denote M.interp ξ0 [] := by
        have h1 : rhs.denote (I'.inst θ) ξ [] =
            rhs.denote (M.interp.inst θ) ξ [] := by
          apply Tm.denote_interp_except (n := n) rhs (I'.inst θ) (M.interp.inst θ)
            ξ [] hrhs_fresh
          intro m α hm
          exact EnvInterp.addDef_inst_of_ne n M.interp ξ0 hrhs θ hm α
        have h2 : rhs.denote (M.interp.inst θ) ξ [] =
            rhs.denote (M.interp.inst θ) (ξ0.pull θ) [] :=
          Tm.denote_no_fvars rhs (M.interp.inst θ) ξ (ξ0.pull θ) [] hclosed
        have h3 := Tm.denote_instTy rhs θ M.interp ξ0 []
        exact (h1.trans h2).trans h3.symm
      have heqI : ∀ α,
          (I'.inst θ).interp eqName (α ↝ α ↝ .bool) =
            zfEq (α.denote (ρ.inst θ)) := fun α => by
        rw [EnvInterp.addDef_inst_of_ne n M.interp ξ0 hrhs θ hne_eq.symm]
        simp [EnvInterp.inst]
        rw [M.eq_ok (α.inst θ)]
        simp [Ty.denote_inst]
      have htyC : HasType (env.addDef n ty rhs) [] (.const n ty) ty :=
        HasType.const (by simp) (Ty.isInstanceOf_self ty)
      have hrhs' : HasType (env.addDef n ty rhs) [] rhs ty :=
        hrhs.weakenEnv (Env.LE.addDef_of_fresh hn)
      apply (Tm.denote_mkEq_true_iff_nil (I'.inst θ) heqI ξ htyC hrhs').2
      calc
        (Tm.const n ty).denote (I'.inst θ) ξ []
            = interpDef M.interp ξ0 ty rhs (ty.inst θ) := hconst_eq
        _   = (rhs.instTy σ).denote M.interp ξ0 [] := hinterp
        _   = (rhs.instTy θ).denote M.interp ξ0 [] := by rw [hinstTy]
        _   = rhs.denote (I'.inst θ) ξ [] := hrhs_den.symm
    | Or.inr hold =>
      have hpT := hwf _ hold
      have hfresh : p.hasConst n = false := hpT.not_hasConst_of_fresh hn
      have hax := M.ax_ok θ p hold ξ
      refine Eq.trans ?_ hax
      apply Tm.denote_interp_except (n := n) p
        (M.interp.addDef (n := n) (FVarVal.ofNonempty hρ) hrhs |>.inst θ)
        (M.interp.inst θ) ξ [] hfresh
      intro m α hm
      exact EnvInterp.addDef_inst_of_ne n M.interp (FVarVal.ofNonempty hρ) hrhs
        θ hm α

theorem Tm.not_free {t : Tm} (h : ∀ x α, t.freeIn x α = false := by intros; rfl)
    (x : Name) (α : Ty) : t.freeIn x α = false :=
  h x α

theorem Tm.tyvars_subset_of_nil {t : Tm} {ty : Ty}
    (h : t.tyvars = [] := by rfl) :
    ∀ x ∈ t.tyvars, x ∈ ty.tyvars := by
  intro x hx
  simp [h] at hx

noncomputable def EnvModel.envTru (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envTru ρ :=
  (EnvModel.holCore ρ hρ).addDef truName hρ truName_fresh_core (by decide)
    holCore_WF HasType.truDef_holCore Tm.not_free Tm.tyvars_subset_of_nil

noncomputable def EnvModel.envAnd (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envAnd ρ :=
  (EnvModel.envTru ρ hρ).addDef andName hρ andName_fresh_envTru (by decide)
    envTru_WF HasType.andDef_envTru Tm.not_free Tm.tyvars_subset_of_nil

noncomputable def EnvModel.envImp (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envImp ρ :=
  (EnvModel.envAnd ρ hρ).addDef impName hρ impName_fresh_envAnd (by decide)
    envAnd_WF HasType.impDef_envAnd Tm.not_free Tm.tyvars_subset_of_nil

noncomputable def EnvModel.envAll (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envAll ρ :=
  (EnvModel.envImp ρ hρ).addDef allName hρ allName_fresh_envImp (by decide)
    envImp_WF HasType.allDef_envImp Tm.not_free (by
      intro x hx
      simp [Tm.allDef, Tm.allExpand, Tm.mkEq, Tm.eqConst, Tm.tru, Tm.tyvars,
        allTy, truTy, Ty.tyvars, primTyVar] at hx ⊢
      exact hx)

noncomputable def EnvModel.envFalsum (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envFalsum ρ :=
  (EnvModel.envAll ρ hρ).addDef falsumName hρ falsumName_fresh_envAll (by decide)
    envAll_WF HasType.falsumDef_envAll Tm.not_free Tm.tyvars_subset_of_nil

noncomputable def EnvModel.envNot (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envNot ρ :=
  (EnvModel.envFalsum ρ hρ).addDef notName hρ notName_fresh_envFalsum (by decide)
    envFalsum_WF HasType.notDef_envFalsum Tm.not_free Tm.tyvars_subset_of_nil

noncomputable def EnvModel.envOr (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envOr ρ :=
  (EnvModel.envNot ρ hρ).addDef orName hρ orName_fresh_envNot (by decide)
    envNot_WF HasType.orDef_envNot Tm.not_free Tm.tyvars_subset_of_nil

noncomputable def EnvModel.envEx (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envEx ρ :=
  (EnvModel.envOr ρ hρ).addDef exName hρ exName_fresh_envOr (by decide)
    envOr_WF HasType.exDef_envOr Tm.not_free (by
      intro x hx
      simp [Tm.exDef, Tm.all, Tm.imp, Tm.tyvars, exTy, impTy, Ty.tyvars,
        primTyVar] at hx ⊢
      exact hx)

noncomputable def EnvModel.envOneOne (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envOneOne ρ :=
  (EnvModel.envEx ρ hρ).addDef oneOneName hρ oneOneName_fresh_envEx (by decide)
    envEx_WF HasType.oneOneDef_envEx Tm.not_free (by
      intro x hx
      simp [Tm.oneOneDef, Tm.all, Tm.imp, Tm.mkEq, Tm.eqConst, Tm.tyvars,
        oneOneTy, impTy, Ty.tyvars, primTyVar, primTyVarB] at hx ⊢
      exact hx)

noncomputable def EnvModel.holLogic (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel holLogic ρ :=
  (EnvModel.envOneOne ρ hρ).addDef ontoName hρ ontoName_fresh_envOneOne (by decide)
    envOneOne_WF HasType.ontoDef_envOneOne Tm.not_free (by
      intro x hx
      simp [Tm.ontoDef, Tm.all, Tm.ex, Tm.mkEq, Tm.eqConst, Tm.tyvars,
        ontoTy, Ty.tyvars, primTyVar, primTyVarB] at hx ⊢
      exact hx)

theorem Provable.sound_holLogic {ρ : TyVal} {Γ p} (h : Γ ⊩[holLogic] p)
    (hρ : ρ.Nonempty) (ξ : FVarVal ρ)
    (hΓ : HypsTrue (EnvModel.holLogic ρ hρ).interp ξ Γ) :
    p.denote (EnvModel.holLogic ρ hρ).interp ξ [] = zfTrue :=
  Provable.sound h (EnvModel.holLogic ρ hρ) ξ hΓ

end HOLean
