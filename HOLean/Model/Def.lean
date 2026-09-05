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

private noncomputable def EnvModel.interpAddAxiom [Env.HasEq env] (M : EnvModel env ρ) (ax : Tm) :
    EnvInterp (env.addAxiom ax) ρ where
  interp := M.interp.interp
  mem := fun hconst => M.interp.mem hconst

private theorem EnvModel.interpAddAxiom_interp [Env.HasEq env] (M : EnvModel env ρ) (ax : Tm)
    (n : Name) (α : Ty) :
    (M.interpAddAxiom ax).interp n α = M.interp.interp n α := rfl

private theorem EnvModel.interpAddAxiom_denote [Env.HasEq env] (M : EnvModel env ρ) (ax : Tm)
    (θ : TySubst) (ξ : FVarVal (ρ.inst θ)) (p : Tm) :
    p.denote ((M.interpAddAxiom ax).inst θ) ξ [] = p.denote (M.interp.inst θ) ξ [] := by
  refine Tm.denote_interp_eq_env p _ _ ξ [] ?_
  intro n α
  simp [EnvInterp.inst, EnvModel.interpAddAxiom_interp]

/-- Interpret a defined constant at an instance of its generic type. -/
noncomputable def interpDef (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (ty : Ty) (rhs : Tm) (inst : Ty) : ZFSet :=
  match ty.matchTy inst [] with
  | some θ => (rhs.instTy θ).denote I ξ []
  | none => ∅

theorem interpDef_mem (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    {ty : Ty} {rhs : Tm} {inst : Ty}
    (hrhs : HasType env [] rhs ty) (hinst : ty.instantiates inst) :
    interpDef I ξ ty rhs inst ∈ inst.denote ρ := by
  have hsome := Ty.matchTy_of_instantiates hinst
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
    · have hconst' : env.lookup m = some gen := by
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

/-- Matching `ty` against `ty.inst θ` recovers `rhs[θ]`, provided every
schematic variable of `rhs` already occurs in `ty`. -/
theorem interpDef_of_inst (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (ty : Ty) (rhs : Tm) (θ : TySubst)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars) :
    interpDef I ξ ty rhs (ty.inst θ) = (rhs.instTy θ).denote I ξ [] := by
  obtain ⟨σ, hσ, hag⟩ := matchTy_inst_agrees ty θ
  simp [interpDef, hσ, instTy_eq_of_match hvars hσ hag]

/-- After `INST_TYPE θ`, the new constant at its generic type is the
interpretation of `rhs` at `ty.inst θ`. -/
theorem EnvInterp.addDef_denote_const (n : Name) {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ0 : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (θ : TySubst) (ξ : FVarVal (ρ.inst θ)) :
    (Tm.const n ty).denote ((I.addDef (n := n) ξ0 hrhs).inst θ) ξ [] =
      interpDef I ξ0 ty rhs (ty.inst θ) := by
  simp [Tm.denote, EnvInterp.inst, EnvInterp.addDef_interp_self]

/-- Terms that do not mention the new constant are interpreted as before. -/
theorem EnvInterp.addDef_denote_except (n : Name) {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ0 : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (θ : TySubst) (ξ : FVarVal (ρ.inst θ))
    (t : Tm) (hfresh : t.hasConst n = false) :
    t.denote ((I.addDef (n := n) ξ0 hrhs).inst θ) ξ [] =
      t.denote (I.inst θ) ξ [] := by
  apply Tm.denote_interp_except (n := n) t
    ((I.addDef (n := n) ξ0 hrhs).inst θ) (I.inst θ) ξ [] hfresh
  intro m α hm
  exact EnvInterp.addDef_inst_of_ne n I ξ0 hrhs θ hm α

/-- A closed RHS denotes the same as its type instance, because it has
no fvars and (being typed in `env`) does not mention the new name. -/
theorem EnvInterp.addDef_denote_rhs (n : Name) {ty : Ty} {rhs : Tm}
    (I : EnvInterp env ρ) (ξ0 : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (θ : TySubst) (ξ : FVarVal (ρ.inst θ))
    (hn : env.lookup n = none)
    (hclosed : ∀ x α, rhs.freeIn x α = false) :
    rhs.denote ((I.addDef (n := n) ξ0 hrhs).inst θ) ξ [] =
      (rhs.instTy θ).denote I ξ0 [] := by
  have h1 :=
    EnvInterp.addDef_denote_except n I ξ0 hrhs θ ξ rhs
      (hrhs.not_hasConst_of_fresh hn)
  have h2 := Tm.denote_no_fvars rhs (I.inst θ) ξ (ξ0.pull θ) [] hclosed
  exact (h1.trans h2).trans (Tm.denote_instTy rhs θ I ξ0 []).symm

/-- Equality stays extensional after `addDef` and `INST_TYPE`. -/
theorem EnvInterp.addDef_inst_eq_ok [Env.HasEq env] (n : Name)
    {ty : Ty} {rhs : Tm} (I : EnvInterp env ρ) (ξ0 : FVarVal ρ)
    (hrhs : HasType env [] rhs ty) (hne_eq : n ≠ eqName)
    (heq : ∀ α, I.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ))
    (θ : TySubst) (α : Ty) :
    ((I.addDef (n := n) ξ0 hrhs).inst θ).interp eqName (α ↝ α ↝ .bool) =
      zfEq (α.denote (ρ.inst θ)) := by
  rw [EnvInterp.addDef_inst_of_ne n I ξ0 hrhs θ hne_eq.symm]
  simp [EnvInterp.inst]
  rw [heq (α.inst θ)]
  simp [Ty.denote_inst]

/-- The new axiom `n = rhs` denotes `zfTrue` at every type instance. -/
theorem EnvModel.addDef_ax_new [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hn : env.lookup n = none) (hne_eq : n ≠ eqName)
    (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    (θ : TySubst) (ξ : FVarVal (ρ.inst θ)) :
    (Tm.mkEq ty (.const n ty) rhs).denote
      ((M.interp.addDef (n := n) (FVarVal.ofNonempty hρ) hrhs).inst θ) ξ [] =
      zfTrue := by
  have : Env.HasEq (env.addDef n ty rhs) := Env.HasEq.addDef hne_eq
  set ξ0 := FVarVal.ofNonempty hρ
  set I' := M.interp.addDef (n := n) ξ0 hrhs
  have htyC : HasType (env.addDef n ty rhs) [] (.const n ty) ty :=
    HasType.const (by simp) (Ty.instantiates_self ty)
  have hrhs' : HasType (env.addDef n ty rhs) [] rhs ty :=
    hrhs.weakenEnv (Env.LE.addDef_of_fresh hn)
  apply (Tm.denote_mkEq_true_iff_nil (I'.inst θ)
    (EnvInterp.addDef_inst_eq_ok n M.interp ξ0 hrhs hne_eq M.eq_ok θ)
    ξ htyC hrhs').2
  calc
    (Tm.const n ty).denote (I'.inst θ) ξ []
        = interpDef M.interp ξ0 ty rhs (ty.inst θ) :=
      EnvInterp.addDef_denote_const n M.interp ξ0 hrhs θ ξ
    _   = (rhs.instTy θ).denote M.interp ξ0 [] :=
      interpDef_of_inst M.interp ξ0 ty rhs θ hvars
    _   = rhs.denote (I'.inst θ) ξ [] :=
      (EnvInterp.addDef_denote_rhs n M.interp ξ0 hrhs θ ξ hn hclosed).symm

/-- Old axioms still denote `zfTrue`: they are well-typed in `env`, so they
do not mention the fresh name, and the two interps agree off `n`. -/
theorem EnvModel.addDef_ax_old [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hn : env.lookup n = none) (hwf : env.WF)
    (hrhs : HasType env [] rhs ty)
    {θ : TySubst} {p : Tm} (hold : p ∈ env.axioms)
    (ξ : FVarVal (ρ.inst θ)) :
    p.denote
      ((M.interp.addDef (n := n) (FVarVal.ofNonempty hρ) hrhs).inst θ) ξ [] =
      zfTrue :=
  (EnvInterp.addDef_denote_except n M.interp (FVarVal.ofNonempty hρ) hrhs
      θ ξ p ((hwf _ hold).not_hasConst_of_fresh hn)).trans
    (M.ax_ok θ p hold ξ)

/-- Transport a model along `addDef`.  The right-hand side must be a closed
term whose schematic variables are among those of the generic type, and
the new name must be fresh (so old axioms do not mention it). -/
noncomputable def EnvModel.addDef [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hn : env.lookup n = none) (hne_eq : n ≠ eqName)
    (hwf : env.WF) (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars) :
    EnvModel (env.addDef n ty rhs) ρ where
  interp := M.interp.addDef (n := n) (FVarVal.ofNonempty hρ) hrhs
  eq_ok :=
    EnvInterp.addDef_eq_ok n M.interp (FVarVal.ofNonempty hρ) hrhs hne_eq M.eq_ok
  ax_ok := fun θ p hp ξ => by
    cases hp with
    | head =>
      exact EnvModel.addDef_ax_new n M hρ hn hne_eq hrhs hclosed hvars θ ξ
    | tail _ hold =>
      exact EnvModel.addDef_ax_old n M hρ hn hwf hrhs hold ξ

/-- Transport a model along `addAxiom`, given a kernel proof of the new sentence. -/
noncomputable def EnvModel.addAxiom [Env.HasEq env] (M : EnvModel env ρ) (_hρ : ρ.Nonempty)
    (ax : Tm) (hax : [] ⊩[env] ax) : EnvModel (env.addAxiom ax) ρ where
  interp := M.interpAddAxiom ax
  eq_ok := fun α => by
    simp [EnvModel.interpAddAxiom_interp]
    exact M.eq_ok α
  ax_ok := fun θ p hp ξ => by
    cases hp with
    | head =>
      have hT := Provable.sound hax (M.inst θ) ξ (fun _ hq => nomatch hq)
      exact (EnvModel.interpAddAxiom_denote M ax θ ξ ax).trans hT
    | tail _ hold =>
      exact (EnvModel.interpAddAxiom_denote M ax θ ξ p).trans (M.ax_ok θ p hold ξ)

theorem EnvModel.addAxiom_interp [Env.HasEq env] (M : EnvModel env ρ) (_hρ : ρ.Nonempty)
    (ax : Tm) (hax : [] ⊩[env] ax) :
    (M.addAxiom _hρ ax hax).interp = M.interpAddAxiom ax := rfl

noncomputable def EnvModel.addDef_checked [Env.HasConnectives env] (n : Name)
    {ty : Ty} {rhs : Tm} (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hfresh : env.lookup n = none) (hne_eq : n ≠ eqName) (hwf : env.WF)
    (hinfer : rhs.infer env [] = some ty) (_hLC : rhs.LC 0 = true)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    (hfree : ∀ x α, rhs.freeIn x α = false) :
    EnvModel (env.addDef n ty rhs) ρ :=
  M.addDef n hρ hfresh hne_eq hwf (HasType.of_infer hinfer) hfree hvars

noncomputable def EnvModel.addDef_cert [Env.HasConnectives env] (n : Name)
    {ty : Ty} {rhs : Tm} (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hfresh : env.lookup n = none) (hne_eq : n ≠ eqName) (hwf : env.WF)
    (hinfer : rhs.infer env [] = some ty) (_hLC : rhs.LC 0 = true)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    (hfree : ∀ x α, rhs.freeIn x α = false) :
    EnvModel (env.addDef n ty rhs) ρ :=
  EnvModel.addDef_checked n M hρ hfresh hne_eq hwf hinfer _hLC hvars hfree

noncomputable def EnvModel.addAxiom_cert [Env.HasEq env] (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (ax : Tm) (hax : [] ⊩[env] ax) :
    EnvModel (env.addAxiom ax) ρ :=
  M.addAxiom hρ ax hax

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
      simp [Tm.allDef_eq, Tm.allExpand, Tm.mkEq, Tm.eqConst, Tm.tru, Tm.tyvars,
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
      simp [Tm.exDef_eq, Tm.all, Tm.imp, Tm.tyvars, exTy, impTy, Ty.tyvars,
        primTyVar] at hx ⊢
      exact hx)

noncomputable def EnvModel.envOneOne (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel envOneOne ρ :=
  (EnvModel.envEx ρ hρ).addDef oneOneName hρ oneOneName_fresh_envEx (by decide)
    envEx_WF HasType.oneOneDef_envEx Tm.not_free (by
      intro x hx
      simp [Tm.oneOneDef_eq, Tm.all, Tm.imp, Tm.mkEq, Tm.eqConst, Tm.tyvars,
        oneOneTy, impTy, Ty.tyvars, primTyVar, primTyVarB] at hx ⊢
      exact hx)

noncomputable def EnvModel.holLogic (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel holLogic ρ :=
  (EnvModel.envOneOne ρ hρ).addDef ontoName hρ ontoName_fresh_envOneOne (by decide)
    envOneOne_WF HasType.ontoDef_envOneOne Tm.not_free (by
      intro x hx
      simp [Tm.ontoDef_eq, Tm.all, Tm.ex, Tm.mkEq, Tm.eqConst, Tm.tyvars,
        ontoTy, Ty.tyvars, primTyVar, primTyVarB] at hx ⊢
      exact hx)

theorem Provable.sound_holLogic {ρ : TyVal} {Γ p} (h : Γ ⊩[holLogic] p)
    (hρ : ρ.Nonempty) (ξ : FVarVal ρ)
    (hΓ : HypsTrue (EnvModel.holLogic ρ hρ).interp ξ Γ) :
    p.denote (EnvModel.holLogic ρ hρ).interp ξ [] = zfTrue :=
  Provable.sound h (EnvModel.holLogic ρ hρ) ξ hΓ

/-- `addDef` does not change the interpretation of a different name. -/
theorem EnvModel.addDef_interp_ne [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (M : EnvModel env ρ) (hρ : ρ.Nonempty)
    (hn : env.lookup n = none) (hne_eq : n ≠ eqName)
    (hwf : env.WF) (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    {m : Name} (hm : m ≠ n) (inst : Ty) :
    (M.addDef n hρ hn hne_eq hwf hrhs hclosed hvars).interp.interp m inst =
      M.interp.interp m inst :=
  EnvInterp.addDef_interp_of_ne n M.interp (FVarVal.ofNonempty hρ) hrhs hm inst

/-- Primitive graphs survive the `addDef` chain. -/
theorem EnvModel.holLogic_interp_prim (ρ : TyVal) (hρ : ρ.Nonempty)
    {n : Name} (hn : n = eqName ∨ n = selectName) (inst : Ty) :
    (EnvModel.holLogic ρ hρ).interp.interp n inst =
      (EnvInterp.holCore ρ hρ).interp n inst := by
  have hne : ∀ (c : Name), c ≠ eqName → c ≠ selectName → n ≠ c := by
    intro c he hs
    cases hn with
    | inl heq =>
      subst heq
      exact he.symm
    | inr hsel =>
      subst hsel
      exact hs.symm
  simp [EnvModel.holLogic, EnvModel.envOneOne, EnvModel.envEx, EnvModel.envOr,
    EnvModel.envNot, EnvModel.envFalsum, EnvModel.envAll, EnvModel.envImp,
    EnvModel.envAnd, EnvModel.envTru, EnvModel.addDef, EnvInterp.addDef,
    EnvModel.holCore,
    hne ontoName (by decide) (by decide),
    hne oneOneName (by decide) (by decide),
    hne exName (by decide) (by decide),
    hne orName (by decide) (by decide),
    hne notName (by decide) (by decide),
    hne falsumName (by decide) (by decide),
    hne allName (by decide) (by decide),
    hne impName (by decide) (by decide),
    hne andName (by decide) (by decide),
    hne truName (by decide) (by decide)]

theorem EnvModel.holLogic_interp_select (ρ : TyVal) (hρ : ρ.Nonempty) (α : Ty) :
    (EnvModel.holLogic ρ hρ).interp.interp selectName ((α ↝ .bool) ↝ α) =
      zfSelect (α.denote ρ) (Ty.denote_nonempty hρ α) :=
  (EnvModel.holLogic_interp_prim ρ hρ (Or.inr rfl) _).trans
    (EnvInterp.holCore_interp_select ρ hρ α)

end HOLean
