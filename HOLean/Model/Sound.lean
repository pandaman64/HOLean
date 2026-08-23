/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Model.Commute

/-!
# Soundness of the HOL Light kernel

If `Γ ⊩[env] p`, `I` models `env`, and every hypothesis denotes `zfTrue`,
then so does the conclusion.  This first instance is `holCore`, which
has no axioms; axiom-carrying environments are transported later along
`addDef`.
-/

open ZFSet Classical

namespace HOLean

/-- A model of an environment at a type valuation: constants land in the
right universes, `eq` is extensional equality, and every axiom (at every
type instance) denotes `zfTrue`. -/
structure EnvModel (env : Env) (ρ : TyVal) where
  interp : EnvInterp env ρ
  eq_ok : ∀ α, interp.interp eqName (α ↝ α ↝ .bool) = zfEq (α.denote ρ)
  ax_ok : ∀ (θ : TySubst) (p : Tm), env.axioms p →
    ∀ ξ : FVarVal (ρ.inst θ), p.denote (interp.inst θ) ξ [] = zfTrue

variable {env : Env}

/-- Hypotheses of a sequent all denote `zfTrue`. -/
def HypsTrue {ρ : TyVal} (I : EnvInterp env ρ) (ξ : FVarVal ρ) (Γ : List Tm) : Prop :=
  ∀ q ∈ Γ, q.denote I ξ [] = zfTrue

theorem HypsTrue.append {ρ : TyVal} {I : EnvInterp env ρ} {ξ : FVarVal ρ}
    {Γ Δ : List Tm} (h : HypsTrue I ξ (Γ ++ Δ)) :
    HypsTrue I ξ Γ ∧ HypsTrue I ξ Δ := by
  constructor
  · intro q hq
    exact h q (List.mem_append.2 (Or.inl hq))
  · intro q hq
    exact h q (List.mem_append.2 (Or.inr hq))

theorem HypsTrue.erase {ρ : TyVal} {I : EnvInterp env ρ} {ξ : FVarVal ρ}
    {Γ : List Tm} {p q : Tm}
    (h : HypsTrue I ξ (hypsErase p Γ)) (hq : q ∈ Γ) (hne : q ≠ p) :
    q.denote I ξ [] = zfTrue :=
  h q (by simp [hypsErase, hq, hne])

theorem TyVal.inst_nonempty {ρ : TyVal} (hρ : ρ.Nonempty) (θ : TySubst) :
    (ρ.inst θ).Nonempty := by
  intro x
  cases h : θ.lookup x with
  | none =>
    simpa [TyVal.inst, h] using hρ x
  | some α =>
    simpa [TyVal.inst, h] using Ty.denote_nonempty hρ α

/-- Lift a model along a type substitution, when the environment has no
axioms (so `ax_ok` is vacuous). -/
noncomputable def EnvModel.inst {ρ : TyVal} (M : EnvModel env ρ) (θ : TySubst)
    (hnone : ∀ p, env.axioms p → False) : EnvModel env (ρ.inst θ) where
  interp := M.interp.inst θ
  eq_ok := fun α => by
    simp [EnvInterp.inst]
    rw [M.eq_ok (α.inst θ)]
    simp [Ty.denote_inst]
  ax_ok := fun _ p hp _ => (hnone p hp).elim

@[simp] theorem EnvModel.inst_interp {ρ : TyVal} (M : EnvModel env ρ)
    (θ : TySubst) (hnone : ∀ p, env.axioms p → False) :
    (M.inst θ hnone).interp = M.interp.inst θ := rfl

/-- `holCore` has a standard model at every nonempty type valuation. -/
noncomputable def EnvModel.holCore (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvModel holCore ρ where
  interp := EnvInterp.holCore ρ hρ
  eq_ok := EnvInterp.holCore_interp_eq ρ hρ
  ax_ok := fun _ _ hp => nomatch hp

theorem holCore_axioms_empty (p : Tm) : holCore.axioms p → False :=
  id

/-- Soundness of the ten rules plus `ax`, for environments without axioms.
`holCore` is the intended instance; `addDef` transport comes next. -/
theorem Provable.sound [Env.HasEq env]
    (hnone : ∀ p, env.axioms p → False)
    {asmΓ asmP} (h : asmΓ ⊩[env] asmP) :
    ∀ {ρ : TyVal} (M : EnvModel env ρ) (ξ : FVarVal ρ),
      HypsTrue M.interp ξ asmΓ → asmP.denote M.interp ξ [] = zfTrue := by
  induction h with
  | refl ht =>
    intro ρ M ξ _hΓ
    exact (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ ht ht).2 rfl
  | trans h1 h2 ih1 ih2 =>
    intro ρ M ξ hΓ
    obtain ⟨hΓ1, hΓ2⟩ := HypsTrue.append hΓ
    obtain ⟨_, hs, ht⟩ := HasType.dest_mkEq (bool_typed h1).2
    obtain ⟨_, _ht', hu⟩ := HasType.dest_mkEq (bool_typed h2).2
    have hst := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hs ht).1
      (ih1 M ξ hΓ1)
    have htu := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ ht hu).1
      (ih2 M ξ hΓ2)
    exact (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hs hu).2
      (hst.trans htu)
  | mkComb h1 h2 ih1 ih2 =>
    intro ρ M ξ hΓ
    obtain ⟨hΓ1, hΓ2⟩ := HypsTrue.append hΓ
    obtain ⟨_, hf, hg⟩ := HasType.dest_mkEq (bool_typed h1).2
    obtain ⟨_, hx, hy⟩ := HasType.dest_mkEq (bool_typed h2).2
    have hfg := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hf hg).1
      (ih1 M ξ hΓ1)
    have hxy := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hx hy).1
      (ih2 M ξ hΓ2)
    exact (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ
      (HasType.app hf hx) (HasType.app hg hy)).2
      (by simp [Tm.denote, hfg, hxy])
  | abs h hfresh ih =>
    intro ρ M ξ hΓ
    rename_i Γ s t x α _β
    obtain ⟨_, hs, ht'⟩ := HasType.dest_mkEq (bool_typed h).2
    apply (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ
      hs.abstract ht'.abstract).2
    apply ext
    intro z
    simp [Tm.abstract, Tm.denote, mem_map]
    constructor
    · intro ⟨v, hv, heq⟩
      refine ⟨v, hv, ?_⟩
      simp [lamFn, hv] at heq ⊢
      have hΓ' : HypsTrue M.interp (ξ.update x α v hv) Γ := by
        intro q hq
        rw [Tm.denote_fresh q M.interp ξ [] hv (hfresh q hq)]
        exact hΓ q hq
      have hst := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok
        (ξ.update x α v hv) hs ht').1
        (ih M (ξ.update x α v hv) hΓ')
      change v.pair (s.close x α |>.denote M.interp ξ [v]) = z at heq
      change v.pair (t.close x α |>.denote M.interp ξ [v]) = z
      rw [Tm.denote_close s M.interp ξ hv hs.lc0] at heq
      rw [Tm.denote_close t M.interp ξ hv ht'.lc0]
      exact hst ▸ heq
    · intro ⟨v, hv, heq⟩
      refine ⟨v, hv, ?_⟩
      simp [lamFn, hv] at heq ⊢
      have hΓ' : HypsTrue M.interp (ξ.update x α v hv) Γ := by
        intro q hq
        rw [Tm.denote_fresh q M.interp ξ [] hv (hfresh q hq)]
        exact hΓ q hq
      have hst := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok
        (ξ.update x α v hv) hs ht').1
        (ih M (ξ.update x α v hv) hΓ')
      change v.pair (s.close x α |>.denote M.interp ξ [v]) = z
      change v.pair (t.close x α |>.denote M.interp ξ [v]) = z at heq
      rw [Tm.denote_close s M.interp ξ hv hs.lc0]
      rw [Tm.denote_close t M.interp ξ hv ht'.lc0] at heq
      exact hst.symm ▸ heq
  | beta ht =>
    intro ρ M ξ _hΓ
    rename_i t x α _β
    have hfvar : HasType env [] (.fvar x α) α := HasType.fvar x α
    exact (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ
      (HasType.app (HasType.lam ht) hfvar) (ht.open' hfvar)).2
      (Tm.denote_beta ht hfvar M.interp ξ)
  | assume hp =>
    intro ρ M ξ hΓ
    exact hΓ _ (List.mem_singleton.2 rfl)
  | eqMp h1 h2 ih1 ih2 =>
    intro ρ M ξ hΓ
    obtain ⟨hΓ1, hΓ2⟩ := HypsTrue.append hΓ
    obtain ⟨_, hp, hq⟩ := HasType.dest_mkEq (bool_typed h1).2
    have hpq := (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hp hq).1
      (ih1 M ξ hΓ1)
    exact hpq ▸ ih2 M ξ hΓ2
  | deductAntisym h1 h2 ih1 ih2 =>
    intro ρ M ξ hΓ
    rename_i Γ Δ p q
    have hpT := (bool_typed h1).2
    have hqT := (bool_typed h2).2
    have hpB := hpT.denote_mem M.interp ξ (CtxVal.nil ρ)
    have hqB := hqT.denote_mem M.interp ξ (CtxVal.nil ρ)
    simp [HasType.denote, CtxVal.nil] at hpB hqB
    have hp_of_hq : q.denote M.interp ξ [] = zfTrue →
        p.denote M.interp ξ [] = zfTrue := by
      intro hq
      apply ih1 M ξ
      intro r hr
      by_cases hrq : r = q
      · exact hrq ▸ hq
      · exact HypsTrue.erase (HypsTrue.append hΓ).1 hr hrq
    have hq_of_hp : p.denote M.interp ξ [] = zfTrue →
        q.denote M.interp ξ [] = zfTrue := by
      intro hp
      apply ih2 M ξ
      intro r hr
      by_cases hrp : r = p
      · exact hrp ▸ hp
      · exact HypsTrue.erase (HypsTrue.append hΓ).2 hr hrp
    apply (Tm.denote_mkEq_true_iff_nil M.interp M.eq_ok ξ hpT hqT).2
    match mem_zfBool.1 hpB, mem_zfBool.1 hqB with
    | Or.inl hpF, Or.inl hqF =>
      rw [hpF, hqF]
    | Or.inl hpF, Or.inr hqTr =>
      have : p.denote M.interp ξ [] = zfTrue := hp_of_hq hqTr
      rw [hpF] at this
      exact (zfFalse_ne_zfTrue this).elim
    | Or.inr hpTr, Or.inl hqF =>
      have : q.denote M.interp ξ [] = zfTrue := hq_of_hp hpTr
      rw [hqF] at this
      exact (zfFalse_ne_zfTrue this).elim
    | Or.inr hpTr, Or.inr hqTr =>
      rw [hpTr, hqTr]
  | instType θ _h ih =>
    intro ρ M ξ hΓ
    rename_i Γ p
    have hΓ' : HypsTrue (M.interp.inst θ) (ξ.pull θ) Γ := by
      intro q hq
      have := hΓ (q.instTy θ) (List.mem_map.2 ⟨q, hq, rfl⟩)
      rwa [Tm.denote_instTy] at this
    have := ih (M.inst θ hnone) (ξ.pull θ) (by simpa using hΓ')
    simpa [Tm.denote_instTy] using this
  | inst hσ h ih =>
    intro ρ M ξ hΓ
    rename_i Γ p σ
    have hΓ' : HypsTrue M.interp (ξ.apply M.interp σ hσ) Γ := by
      intro q hq
      have hqT := (bool_typed h).1 q hq
      have := hΓ (q.applySubst σ) (List.mem_map.2 ⟨q, hq, rfl⟩)
      have heq := HasType.denote_applySubst hqT hσ M.interp ξ (CtxVal.nil ρ)
      simp [CtxVal.nil] at heq this
      rwa [← heq]
    have := ih M (ξ.apply M.interp σ hσ) hΓ'
    have hpT := (bool_typed h).2
    have heq := HasType.denote_applySubst hpT hσ M.interp ξ (CtxVal.nil ρ)
    simp [CtxVal.nil] at heq this
    rwa [heq]
  | ax hp _hty =>
    intro _ρ _M _ξ _hΓ
    exact (hnone _ hp).elim

theorem Provable.sound_holCore {ρ : TyVal} {Γ p} (h : Γ ⊩[holCore] p)
    (hρ : ρ.Nonempty) (ξ : FVarVal ρ)
    (hΓ : HypsTrue (EnvInterp.holCore ρ hρ) ξ Γ) :
    p.denote (EnvInterp.holCore ρ hρ) ξ [] = zfTrue :=
  Provable.sound holCore_axioms_empty h (EnvModel.holCore ρ hρ) ξ hΓ

end HOLean
