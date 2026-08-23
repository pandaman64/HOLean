/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Connective
import HOLean.Kernel
import HOLean.Syntax.Logic

/-!
# Derived rules

The HOL Light kernel is equality-based.  This module recovers the first
useful layer: symmetry of `=`, `|- T`, `p` implies `p = T`, general β,
conjunction, both projections, `MP`, hypothesis weakening, and
generalization.

α-equivalent named terms are already *equal* as `Tm` values (binders are
indices).  There is no separate α-equivalence relation.
-/

namespace HOLean

theorem Tm.abstract_app_app_fvar (x : Name) (α : Ty) (p q : Tm)
    (hp : p.freeIn x α = false) (hq : q.freeIn x α = false) :
    ((fvar x α).app p |>.app q).abstract x α =
      Tm.lam α ((Tm.bvar 0).app p |>.app q) := by
  simp [Tm.abstract, Tm.close, Tm.closeAt, Tm.closeAt_fresh hp, Tm.closeAt_fresh hq]

theorem Tm.openAt_substFvar (t : Tm) (k : Nat) (x : Name) (α : Ty) (u : Tm)
    (hf : t.freeIn x α = false) :
    (t.openAt k (.fvar x α)).substFvar x α u = t.openAt k u := by
  induction t generalizing k with
  | bvar i =>
    by_cases hi : i = k
    · simp [Tm.openAt, Tm.substFvar, hi]
    · simp [Tm.openAt, hi]
  | fvar y β =>
    simp [Tm.freeIn] at hf
    by_cases hy : y = x ∧ β = α
    · exact (hf hy.1 hy.2).elim
    · simp [Tm.openAt, Tm.substFvar, hy]
  | const c β =>
    simp [Tm.openAt]
  | app f a ihf iha =>
    simp [Tm.freeIn] at hf
    simp [Tm.openAt, Tm.substFvar, ihf k hf.1, iha k hf.2]
  | lam β t ih =>
    simp [Tm.freeIn] at hf
    simp [Tm.openAt, Tm.substFvar, ih (k + 1) hf]

theorem Tm.open_subst_fvar (t : Tm) (x : Name) (α : Ty) (u : Tm)
    (hf : t.freeIn x α = false) :
    (t.open' (.fvar x α)).substFvar x α u = t.open' u :=
  t.openAt_substFvar 0 x α u hf

private theorem ne_pair_symm {x y : Name} {α β : Ty}
    (h : ¬ (y = x ∧ β = α)) : ¬ (x = y ∧ α = β) :=
  fun ⟨hxy, hab⟩ => h ⟨hxy.symm, hab.symm⟩

theorem Tm.applySubst_singleton (t : Tm) (x : Name) (α : Ty) (u : Tm) :
    t.applySubst [(x, α, u)] = t.substFvar x α u := by
  induction t with
  | bvar i => simp [Tm.applySubst, Tm.substFvar]
  | fvar y β =>
    unfold Tm.applySubst Tm.substFvar Tm.Subst.lookup
    by_cases h : y = x ∧ β = α
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h, ne_pair_symm h, Tm.Subst.lookup]
  | const c β => simp [Tm.applySubst, Tm.substFvar]
  | app f a ihf iha => simp [Tm.applySubst, Tm.substFvar, ihf, iha]
  | lam β t ih => simp [Tm.applySubst, Tm.substFvar, ih]

theorem Tm.applySubst_fresh (t : Tm) (x : Name) (α : Ty) (u : Tm)
    (hf : t.freeIn x α = false) : t.applySubst [(x, α, u)] = t := by
  induction t with
  | bvar i => simp [Tm.applySubst]
  | fvar y β =>
    simp [Tm.freeIn] at hf
    by_cases hy : y = x ∧ β = α
    · exact (hf hy.1 hy.2).elim
    · simp [Tm.applySubst, Tm.Subst.lookup, ne_pair_symm hy]
  | const c β => simp [Tm.applySubst]
  | app f a ihf iha =>
    simp [Tm.freeIn] at hf
    simp [Tm.applySubst, ihf hf.1, iha hf.2]
  | lam β t ih =>
    simp [Tm.freeIn] at hf
    simp [Tm.applySubst, ih hf]

theorem Tm.open_and_body (p q u : Tm) (hp : p.LC 0 = true) (hq : q.LC 0 = true) :
    ((((Tm.bvar 0).app p).app q).open' u) = ((u.app p).app q) := by
  simp [Tm.open', Tm.openAt, Tm.openAt_of_LC hp, Tm.openAt_of_LC hq]

theorem Tm.mkEq_instTy (α : Ty) (s t : Tm) (θ : TySubst) :
    (mkEq α s t).instTy θ = mkEq (α.inst θ) (s.instTy θ) (t.instTy θ) :=
  rfl

theorem Tm.tru_instTy (θ : TySubst) : tru.instTy θ = tru := rfl

theorem Tm.andExpand_openAt_fst {p : Tm} (hp : p.LC 0 = true) :
    (andExpand (bvar 1) (bvar 0)).openAt 1 p = andExpand p (bvar 0) := by
  simp [andExpand, mkEq, eqConst, boolCombTy, shift, openAt, tru, shift_of_LC0 hp]

theorem Tm.andExpand_bvars_open {p q : Tm}
    (hp : p.LC 0 = true) (hq : q.LC 0 = true) :
    ((andExpand (bvar 1) (bvar 0)).openAt 1 p).openAt 0 q = andExpand p q := by
  rw [andExpand_openAt_fst hp]
  simp [andExpand, mkEq, eqConst, boolCombTy, shift, openAt, tru,
    shift_of_LC0 hp, shift_of_LC0 hq,
    openAt_of_LC (t := p) (LC_le hp (Nat.zero_le _))]

theorem Tm.impExpand_openAt_fst {p : Tm} (_hp : p.LC 0 = true) :
    (impExpand (bvar 1) (bvar 0)).openAt 1 p = impExpand p (bvar 0) := by
  simp [impExpand, and, mkEq, eqConst, openAt]

theorem Tm.impExpand_bvars_open {p q : Tm}
    (hp : p.LC 0 = true) (_hq : q.LC 0 = true) :
    ((impExpand (bvar 1) (bvar 0)).openAt 1 p).openAt 0 q = impExpand p q := by
  rw [impExpand_openAt_fst hp]
  simp [impExpand, and, mkEq, eqConst, openAt, openAt_of_LC hp]

theorem Tm.allExpand_bvar_open (α : Ty) (P : Tm) :
    (allExpand α (bvar 0)).open' P = allExpand α P := by
  simp [allExpand, mkEq, eqConst, openAt, tru]

theorem Tm.allTy_inst (α : Ty) :
    allTy.inst [(primTyVar, α)] = (α ↝ .bool) ↝ .bool := by
  simp [allTy, primTyVar, Ty.inst, TySubst.lookup]

theorem Tm.allDef_instTy (α : Ty) :
    allDef.instTy [(primTyVar, α)] =
      lam (α ↝ .bool) (allExpand α (bvar 0)) := by
  simp [allDef_eq, allExpand, mkEq, eqConst, tru, truTy, primTyVar,
    instTy, Ty.inst, TySubst.lookup]

theorem Tm.all_ax_instTy (α : Ty) :
    (mkEq allTy (.const allName allTy) allDef).instTy [(primTyVar, α)] =
      mkEq ((α ↝ .bool) ↝ .bool)
        (.const allName ((α ↝ .bool) ↝ .bool))
        (lam (α ↝ .bool) (allExpand α (bvar 0))) := by
  simp [mkEq, eqConst, allTy_inst, allDef_instTy, Ty.inst]

variable {env : Env} [Env.HasConnectives env]
set_option linter.unusedSectionVars false

namespace Provable

theorem eq_sym {Γ s t α} (h : Γ ⊩[env] Tm.mkEq α s t) : Γ ⊩[env] Tm.mkEq α t s := by
  obtain ⟨_, hs, _ht⟩ := HasType.dest_mkEq h.concl_bool
  have hrefl_eq : [] ⊩[env] Tm.mkEq (α ↝ α ↝ .bool) (Tm.eqConst α) (Tm.eqConst α) :=
    refl (HasType.eqConst α)
  have hfun : Γ ⊩[env] Tm.mkEq (α ↝ .bool) ((Tm.eqConst α).app s) ((Tm.eqConst α).app t) := by
    simpa [Tm.eqConst] using mkComb hrefl_eq h
  have hrefl_s : [] ⊩[env] Tm.mkEq α s s := refl hs
  have hboolEq : Γ ⊩[env] Tm.mkEq .bool (Tm.mkEq α s s) (Tm.mkEq α t s) := by
    simpa [Tm.mkEq] using mkComb hfun hrefl_s
  simpa [Tm.mkEq] using eqMp hboolEq hrefl_s

theorem tru_ax_typed : HasType env [] (Tm.mkEq truTy Tm.tru Tm.truDef) .bool :=
  HasType.mkEq HasType.tru HasType.truExpand

theorem tru_eq_def : [] ⊩[env] Tm.mkEq .bool Tm.tru Tm.truDef :=
  ax Env.HasConnectives.tru_ax tru_ax_typed

theorem truExpand_intro : [] ⊩[env] Tm.truExpand :=
  refl (HasType.lam (HasType.bvar (by simp)))

theorem tru_intro : [] ⊩[env] Tm.tru :=
  eqMp (eq_sym tru_eq_def) truExpand_intro

/-- Raw form: `DEDUCT_ANTISYM` against `⊢ T` drops `T` if it was assumed. -/
theorem eqt_intro_erase {Γ p} (h : Γ ⊩[env] p) :
    hypsErase Tm.tru Γ ⊩[env] Tm.mkEq .bool p Tm.tru := by
  simpa [hypsErase] using deductAntisym h tru_intro

/-- `Γ ⊢ p` implies `Γ ⊢ p = T`.

The kernel rule behind this is `DEDUCT_ANTISYM` with `⊢ T`, whose conclusion
has hypotheses `Γ \ {T}`.  `T` is object-logic truth, not an assumption, so
the side condition recovers the original list. -/
theorem eqt_intro {Γ p} (h : Γ ⊩[env] p) (hT : Tm.tru ∉ Γ) :
    Γ ⊩[env] Tm.mkEq .bool p Tm.tru :=
  hypsErase_eq_of_not_mem hT ▸ eqt_intro_erase h

theorem beta_conv {t u : Tm} {x : Name} {α β : Ty}
    (ht : HasType env [α] t β) (hu : HasType env [] u α)
    (hf : t.freeIn x α = false) :
    [] ⊩[env] Tm.mkEq β ((Tm.lam α t).app u) (t.open' u) := by
  have hβ := beta (t := t) (x := x) (α := α) (β := β) ht
  have hσ : Tm.Subst.Ok env [(x, α, u)] := by
    intro y γ v hv
    simp [Tm.Subst.lookup] at hv
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hv
    exact hu
  have hinst := inst (σ := [(x, α, u)]) hσ hβ
  have hconcl :
      (Tm.mkEq β ((Tm.lam α t).app (Tm.fvar x α)) (t.open' (Tm.fvar x α))).applySubst
          [(x, α, u)] =
        Tm.mkEq β ((Tm.lam α t).app u) (t.open' u) := by
    simp [Tm.mkEq, Tm.applySubst, Tm.Subst.lookup, Tm.applySubst_fresh t x α u hf]
    rw [Tm.applySubst_singleton, Tm.openAt_substFvar t 0 x α u hf]
  exact hconcl ▸ hinst

/-! Unfolding definitional connectives (`⊢ c = t`, then β). -/

theorem and_ax_typed :
    HasType env [] (Tm.mkEq andTy (.const andName andTy) Tm.andDef) .bool :=
  HasType.mkEq HasType.andConst HasType.andDef

theorem and_const_eq_def :
    [] ⊩[env] Tm.mkEq andTy (.const andName andTy) Tm.andDef :=
  ax Env.HasConnectives.and_ax and_ax_typed

theorem HasType.andDef_inner :
    HasType env [.bool] (Tm.lam .bool (Tm.andExpand (.bvar 1) (.bvar 0)))
      (.bool ↝ .bool) :=
  HasType.lam (HasType.andExpand (HasType.bvar (by simp)) (HasType.bvar (by simp)))

theorem andDef_beta1 {p : Tm} (x : Name)
    (hp : HasType env [] p .bool) :
    [] ⊩[env] Tm.mkEq (.bool ↝ .bool)
      (Tm.andDef.app p)
      (Tm.lam .bool ((Tm.andExpand (.bvar 1) (.bvar 0)).openAt 1 p)) := by
  have hβ :=
    beta_conv (t := Tm.lam .bool (Tm.andExpand (.bvar 1) (.bvar 0)))
      (u := p) (x := x) (α := .bool) (β := .bool ↝ .bool)
      HasType.andDef_inner hp (by
        simp [Tm.andExpand, Tm.mkEq, Tm.freeIn, Tm.shift, Tm.shift_of_LC0 Tm.tru_LC,
          Tm.tru_not_free])
  simpa [Tm.andDef_eq, Tm.open', Tm.openAt] using hβ

theorem HasType.andExpand_open_fst {p : Tm}
    (hp : HasType env [] p .bool) :
    HasType env [.bool] ((Tm.andExpand (.bvar 1) (.bvar 0)).openAt 1 p) .bool := by
  rw [Tm.andExpand_openAt_fst hp.lc0]
  exact HasType.andExpand hp.of_closed (HasType.bvar (by simp))

theorem andDef_beta2 {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam .bool ((Tm.andExpand (.bvar 1) (.bvar 0)).openAt 1 p)).app q)
      (p.andExpand q) := by
  have hβ :=
    beta_conv (t := (Tm.andExpand (.bvar 1) (.bvar 0)).openAt 1 p)
      (u := q) (x := x) (α := .bool) (β := .bool)
      (HasType.andExpand_open_fst hp) hq (by
        rw [Tm.andExpand_openAt_fst hp.lc0]
        simp [Tm.andExpand, Tm.freeIn, Tm.shift, Tm.shift_of_LC0 hp.lc0,
          Tm.shift_of_LC0 Tm.tru_LC, Tm.tru_not_free, hxp])
  simpa [Tm.andExpand_bvars_open hp.lc0 hq.lc0] using hβ

theorem andDef_app_eq_expand {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool ((Tm.andDef.app p).app q) (p.andExpand q) := by
  have h1 := andDef_beta1 (p := p) x hp
  have h2 := mkComb h1 (refl hq)
  have h3 := andDef_beta2 (p := p) (q := q) x hp hq hxp
  simpa using trans h2 h3

theorem and_eq_expand {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool (p.and q) (p.andExpand q) := by
  have happ :=
    mkComb (mkComb and_const_eq_def (refl hp)) (refl hq)
  have hβ := andDef_app_eq_expand (p := p) (q := q) x hp hq hxp
  have happ' : [] ⊩[env] Tm.mkEq .bool (p.and q) ((Tm.andDef.app p).app q) := by
    simpa [Tm.and] using happ
  simpa using trans happ' hβ

theorem imp_ax_typed :
    HasType env [] (Tm.mkEq impTy (.const impName impTy) Tm.impDef) .bool :=
  HasType.mkEq HasType.impConst HasType.impDef

theorem imp_const_eq_def :
    [] ⊩[env] Tm.mkEq impTy (.const impName impTy) Tm.impDef :=
  ax Env.HasConnectives.imp_ax imp_ax_typed

theorem HasType.impDef_inner :
    HasType env [.bool] (Tm.lam .bool (Tm.impExpand (.bvar 1) (.bvar 0)))
      (.bool ↝ .bool) :=
  HasType.lam (HasType.impExpand (HasType.bvar (by simp)) (HasType.bvar (by simp)))

theorem impDef_beta1 {p : Tm} (x : Name)
    (hp : HasType env [] p .bool) :
    [] ⊩[env] Tm.mkEq (.bool ↝ .bool)
      (Tm.impDef.app p)
      (Tm.lam .bool ((Tm.impExpand (.bvar 1) (.bvar 0)).openAt 1 p)) := by
  have hβ :=
    beta_conv (t := Tm.lam .bool (Tm.impExpand (.bvar 1) (.bvar 0)))
      (u := p) (x := x) (α := .bool) (β := .bool ↝ .bool)
      HasType.impDef_inner hp (by simp [Tm.impExpand, Tm.and, Tm.mkEq, Tm.freeIn])
  simpa [Tm.impDef_eq, Tm.open', Tm.openAt] using hβ

theorem HasType.impExpand_open_fst {p : Tm}
    (hp : HasType env [] p .bool) :
    HasType env [.bool] ((Tm.impExpand (.bvar 1) (.bvar 0)).openAt 1 p) .bool := by
  rw [Tm.impExpand_openAt_fst hp.lc0]
  exact HasType.impExpand hp.of_closed (HasType.bvar (by simp))

theorem impDef_beta2 {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam .bool ((Tm.impExpand (.bvar 1) (.bvar 0)).openAt 1 p)).app q)
      (p.impExpand q) := by
  have hβ :=
    beta_conv (t := (Tm.impExpand (.bvar 1) (.bvar 0)).openAt 1 p)
      (u := q) (x := x) (α := .bool) (β := .bool)
      (HasType.impExpand_open_fst hp) hq (by
        rw [Tm.impExpand_openAt_fst hp.lc0]
        simp [Tm.impExpand, Tm.and, Tm.freeIn, hxp])
  simpa [Tm.impExpand_bvars_open hp.lc0 hq.lc0] using hβ

theorem imp_eq_expand {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool (p.imp q) (p.impExpand q) := by
  have happ :=
    mkComb (mkComb imp_const_eq_def (refl hp)) (refl hq)
  have h1 := impDef_beta1 (p := p) x hp
  have h2 := mkComb h1 (refl hq)
  have h3 := impDef_beta2 (p := p) (q := q) x hp hq hxp
  have happ' : [] ⊩[env] Tm.mkEq .bool (p.imp q) ((Tm.impDef.app p).app q) := by
    simpa [Tm.imp] using happ
  have hβ : [] ⊩[env] Tm.mkEq .bool ((Tm.impDef.app p).app q) (p.impExpand q) := by
    simpa using trans h2 h3
  simpa using trans happ' hβ

theorem all_ax_typed :
    HasType env [] (Tm.mkEq allTy (.const allName allTy) Tm.allDef) .bool :=
  HasType.mkEq (HasType.allConst (.var primTyVar)) HasType.allDef

theorem all_const_eq_def :
    [] ⊩[env] Tm.mkEq allTy (.const allName allTy) Tm.allDef :=
  ax Env.HasConnectives.all_ax all_ax_typed

theorem all_const_eq_def_inst (α : Ty) :
    [] ⊩[env] Tm.mkEq ((α ↝ .bool) ↝ .bool)
      (.const allName ((α ↝ .bool) ↝ .bool))
      (Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0))) :=
  Tm.all_ax_instTy α ▸ instType [(primTyVar, α)] all_const_eq_def

theorem HasType.allDef_inst_inner (α : Ty) :
    HasType env [α ↝ .bool] (Tm.allExpand α (.bvar 0)) .bool :=
  HasType.allExpand (α := α) (HasType.bvar (by simp))

theorem all_eq_expand (α : Ty) {P : Tm} (x : Name)
    (hP : HasType env [] P (α ↝ .bool)) :
    [] ⊩[env] Tm.mkEq .bool (Tm.all α P) (Tm.allExpand α P) := by
  have happ := mkComb (all_const_eq_def_inst α) (refl hP)
  have hβ :=
    beta_conv (t := Tm.allExpand α (.bvar 0)) (u := P) (x := x)
      (α := α ↝ .bool) (β := .bool)
      (HasType.allDef_inst_inner α) hP (by simp [Tm.allExpand, Tm.freeIn, Tm.tru_not_free])
  have happ' :
      [] ⊩[env] Tm.mkEq .bool (Tm.all α P)
        ((Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0))).app P) := by
    simpa [Tm.all] using happ
  have hβ' :
      [] ⊩[env] Tm.mkEq .bool
        ((Tm.lam (α ↝ .bool) (Tm.allExpand α (.bvar 0))).app P)
        (Tm.allExpand α P) :=
    Tm.allExpand_bvar_open α P ▸ hβ
  simpa using trans happ' hβ'

theorem gen {Γ t x α} (h : Γ ⊩[env] t)
    (hT : Tm.tru ∉ Γ)
    (hfresh : ∀ r ∈ Γ, r.freeIn x α = false) :
    Γ ⊩[env] Tm.all α (t.abstract x α) := by
  have hTfree : Tm.tru.freeIn x α = false := Tm.tru_not_free x α
  have habs := abs (eqt_intro h hT) hfresh
  have htruAbs : Tm.tru.abstract x α = Tm.lam α Tm.tru := by
    simp [Tm.abstract, Tm.close, Tm.closeAt_fresh (t := Tm.tru) hTfree]
  have hexp : Γ ⊩[env] Tm.allExpand α (t.abstract x α) := by
    simpa [Tm.allExpand, htruAbs] using habs
  have htAbs : HasType env [] (t.abstract x α) (α ↝ .bool) := by
    obtain ⟨_, hs, _⟩ := HasType.dest_mkEq habs.concl_bool
    exact hs
  have hunf := all_eq_expand α x htAbs
  simpa using eqMp (eq_sym hunf) hexp

theorem conj {Γ Δ p q : _} (x : Name)
    (hp : Γ ⊩[env] p) (hq : Δ ⊩[env] q)
    (hTΓ : Tm.tru ∉ Γ) (hTΔ : Tm.tru ∉ Δ)
    (hxΓ : ∀ r ∈ Γ, r.freeIn x Tm.boolCombTy = false)
    (hxΔ : ∀ r ∈ Δ, r.freeIn x Tm.boolCombTy = false)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxpBool : p.freeIn x .bool = false) :
    (Γ ++ Δ) ⊩[env] p.and q := by
  have hpT := eqt_intro hp hTΓ
  have hqT := eqt_intro hq hTΔ
  have hp0 : p.LC 0 = true := hp.concl_bool.lc0
  have hq0 : q.LC 0 = true := hq.concl_bool.lc0
  have hT0 : Tm.tru.LC 0 = true := Tm.tru_LC
  have hf : [] ⊩[env] Tm.mkEq Tm.boolCombTy (Tm.fvar x Tm.boolCombTy) (Tm.fvar x Tm.boolCombTy) :=
    refl (HasType.fvar x Tm.boolCombTy)
  have h1 := mkComb hf hpT
  have h2 := mkComb h1 hqT
  have hfresh : ∀ r ∈ Γ ++ Δ, r.freeIn x Tm.boolCombTy = false := by
    intro r hr
    match List.mem_append.1 hr with
    | Or.inl hr => exact hxΓ r hr
    | Or.inr hr => exact hxΔ r hr
  have h2' :
      Γ ++ Δ ⊩[env]
        Tm.mkEq .bool
          (((Tm.fvar x Tm.boolCombTy).app p).app q)
          (((Tm.fvar x Tm.boolCombTy).app Tm.tru).app Tm.tru) := by
    simpa using h2
  have habs := abs h2' hfresh
  have hpq := Tm.abstract_app_app_fvar x Tm.boolCombTy p q hxp hxq
  have hTT :=
    Tm.abstract_app_app_fvar x Tm.boolCombTy Tm.tru Tm.tru
      (Tm.tru_not_free _ _) (Tm.tru_not_free _ _)
  have hexp : (Γ ++ Δ) ⊩[env] p.andExpand q := by
    have hand :
        p.andExpand q =
          Tm.mkEq (Tm.boolCombTy ↝ .bool)
            ((((Tm.fvar x Tm.boolCombTy).app p).app q).abstract x Tm.boolCombTy)
            ((((Tm.fvar x Tm.boolCombTy).app Tm.tru).app Tm.tru).abstract x Tm.boolCombTy) := by
      unfold Tm.andExpand
      simp only [Tm.shift_of_LC0 hp0, Tm.shift_of_LC0 hq0, Tm.shift_of_LC0 hT0]
      rw [← hpq, ← hTT]
    exact hand ▸ habs
  have hunf := and_eq_expand x hp.concl_bool hq.concl_bool hxpBool
  simpa using eqMp (eq_sym hunf) hexp

def projSnd : Tm :=
  Tm.lam .bool (Tm.lam .bool (Tm.bvar 0))

def projFst : Tm :=
  Tm.lam .bool (Tm.lam .bool (Tm.bvar 1))

theorem hasType_projSnd : HasType env [] projSnd Tm.boolCombTy :=
  HasType.lam (HasType.lam (HasType.bvar (by simp)))

theorem hasType_projFst : HasType env [] projFst Tm.boolCombTy :=
  HasType.lam (HasType.lam (HasType.bvar (by simp)))

theorem and_lhs_type {p q} (hp : HasType env [] p .bool) (hq : HasType env [] q .bool) :
    HasType env [Tm.boolCombTy] (((Tm.bvar 0).app p).app q) .bool := by
  unfold Tm.boolCombTy
  exact HasType.app (HasType.app (HasType.bvar (by simp)) hp.of_closed) hq.of_closed

theorem and_rhs_type :
    HasType env [Tm.boolCombTy] (((Tm.bvar 0).app Tm.tru).app Tm.tru) .bool := by
  unfold Tm.boolCombTy
  exact HasType.app (HasType.app (HasType.bvar (by simp)) HasType.tru) HasType.tru

theorem and_eq_combinators {p q}
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool) :
    p.andExpand q =
      Tm.mkEq (Tm.boolCombTy ↝ .bool)
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q))
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)) := by
  simp [Tm.andExpand, Tm.shift_of_LC0 hp.lc0, Tm.shift_of_LC0 hq.lc0, Tm.shift_of_LC0 Tm.tru_LC]

/-- `(λ f. f p q) u = u p q` by general β. -/
theorem comb_beta {p q u : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hu : HasType env [] u Tm.boolCombTy)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false) :
    [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app u)
      ((u.app p).app q) := by
  have hβ :=
    beta_conv (t := ((Tm.bvar 0).app p).app q) (u := u) (x := x)
      (α := Tm.boolCombTy) (β := .bool)
      (and_lhs_type hp hq) hu (by simp [Tm.freeIn, hxp, hxq])
  have hopen :
      ((((Tm.bvar 0).app p).app q).open' u) = ((u.app p).app q) :=
    Tm.open_and_body p q u hp.lc0 hq.lc0
  exact hopen ▸ hβ

theorem projFst_beta {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool ((projFst.app p).app q) p := by
  have ht : HasType env [.bool] (Tm.lam .bool (Tm.bvar 1)) (.bool ↝ .bool) :=
    HasType.lam (HasType.bvar (by simp))
  have h1 :=
    beta_conv (t := Tm.lam .bool (Tm.bvar 1)) (u := p) (x := x)
      (α := .bool) (β := .bool ↝ .bool) ht hp (by simp [Tm.freeIn])
  have h1' : [] ⊩[env] Tm.mkEq (.bool ↝ .bool) (projFst.app p) (Tm.lam .bool p) := by
    simpa [projFst, Tm.open', Tm.openAt] using h1
  have h2 : [] ⊩[env] Tm.mkEq .bool ((projFst.app p).app q) ((Tm.lam .bool p).app q) := by
    simpa using mkComb h1' (refl hq)
  have h3 :=
    beta_conv (t := p) (u := q) (x := x) (α := .bool) (β := .bool)
      hp.of_closed hq hxp
  have h3' : [] ⊩[env] Tm.mkEq .bool ((Tm.lam .bool p).app q) p := by
    simpa [Tm.openAt_of_LC hp.lc0] using h3
  simpa using trans h2 h3'

theorem projSnd_beta {p q : Tm} (x : Name)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (_hxq : q.freeIn x .bool = false) :
    [] ⊩[env] Tm.mkEq .bool ((projSnd.app p).app q) q := by
  have ht : HasType env [.bool] (Tm.lam .bool (Tm.bvar 0)) (.bool ↝ .bool) :=
    HasType.lam (HasType.bvar (by simp))
  have h1 :=
    beta_conv (t := Tm.lam .bool (Tm.bvar 0)) (u := p) (x := x)
      (α := .bool) (β := .bool ↝ .bool) ht hp (by simp [Tm.freeIn])
  have h1' : [] ⊩[env] Tm.mkEq (.bool ↝ .bool) (projSnd.app p) (Tm.lam .bool (Tm.bvar 0)) := by
    simpa [projSnd, Tm.open', Tm.openAt] using h1
  have h2 : [] ⊩[env] Tm.mkEq .bool ((projSnd.app p).app q) ((Tm.lam .bool (Tm.bvar 0)).app q) := by
    simpa using mkComb h1' (refl hq)
  have h3 :=
    beta_conv (t := Tm.bvar 0) (u := q) (x := x) (α := .bool) (β := .bool)
      (HasType.bvar (by simp)) hq (by simp [Tm.freeIn])
  have h3' : [] ⊩[env] Tm.mkEq .bool ((Tm.lam .bool (Tm.bvar 0)).app q) q := by
    simpa [Tm.open', Tm.openAt] using h3
  simpa using trans h2 h3'

/-- Left projection: `Γ ⊢ p ∧ q` gives `Γ ⊢ p`. -/
theorem and_elim_left {Γ p q} (x : Name)
    (h : Γ ⊩[env] p.and q)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxpBool : p.freeIn x .bool = false) :
    Γ ⊩[env] p := by
  have hexp : Γ ⊩[env] p.andExpand q :=
    eqMp (and_eq_expand x hp hq hxpBool) h
  have heq :
      Γ ⊩[env] Tm.mkEq (Tm.boolCombTy ↝ .bool)
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q))
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)) :=
    (and_eq_combinators hp hq) ▸ hexp
  have happ :
      Γ ⊩[env] Tm.mkEq .bool
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projFst)
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projFst) := by
    simpa using mkComb heq (refl hasType_projFst)
  have hl := comb_beta (p := p) (q := q) (u := projFst) x hp hq hasType_projFst hxp hxq
  have hr :=
    comb_beta (p := Tm.tru) (q := Tm.tru) (u := projFst) x
      (HasType.tru (env := env)) (HasType.tru (env := env)) hasType_projFst
      (Tm.tru_not_free _ _) (Tm.tru_not_free _ _)
  have hπp := projFst_beta x hp hq hxpBool
  have hπT := projFst_beta (p := Tm.tru) (q := Tm.tru) x
    (HasType.tru (env := env)) (HasType.tru (env := env))
    (Tm.tru_not_free x .bool)
  have hl' : [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projFst) p :=
    trans hl hπp
  have hr' : [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projFst) Tm.tru :=
    trans hr hπT
  have hpT : Γ ⊩[env] Tm.mkEq .bool p Tm.tru := by
    have h1 := trans (eq_sym hl') happ
    simpa using trans h1 hr'
  simpa using eqMp (eq_sym hpT) tru_intro

/-- Right projection: `Γ ⊢ p ∧ q` gives `Γ ⊢ q`. -/
theorem and_elim_right {Γ p q} (x : Name)
    (h : Γ ⊩[env] p.and q)
    (hp : HasType env [] p .bool) (hq : HasType env [] q .bool)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxpBool : p.freeIn x .bool = false)
    (hxqBool : q.freeIn x .bool = false) :
    Γ ⊩[env] q := by
  have hexp : Γ ⊩[env] p.andExpand q :=
    eqMp (and_eq_expand x hp hq hxpBool) h
  have heq :
      Γ ⊩[env] Tm.mkEq (Tm.boolCombTy ↝ .bool)
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q))
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)) :=
    (and_eq_combinators hp hq) ▸ hexp
  have happ :
      Γ ⊩[env] Tm.mkEq .bool
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projSnd)
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projSnd) := by
    simpa using mkComb heq (refl hasType_projSnd)
  have hl := comb_beta (p := p) (q := q) (u := projSnd) x hp hq hasType_projSnd hxp hxq
  have hr :=
    comb_beta (p := Tm.tru) (q := Tm.tru) (u := projSnd) x
      (HasType.tru (env := env)) (HasType.tru (env := env)) hasType_projSnd
      (Tm.tru_not_free _ _) (Tm.tru_not_free _ _)
  have hπq := projSnd_beta x hp hq hxqBool
  have hπT := projSnd_beta (p := Tm.tru) (q := Tm.tru) x
    (HasType.tru (env := env)) (HasType.tru (env := env))
    (Tm.tru_not_free x .bool)
  have hl' : [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projSnd) q :=
    trans hl hπq
  have hr' : [] ⊩[env] Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projSnd) Tm.tru :=
    trans hr hπT
  have hqT : Γ ⊩[env] Tm.mkEq .bool q Tm.tru := by
    have h1 := trans (eq_sym hl') happ
    simpa using trans h1 hr'
  simpa using eqMp (eq_sym hqT) tru_intro

/-- Modus ponens from `p ⇒ q ≔ (p ∧ q) = p`. -/
theorem mp {Γ Δ p q} (x : Name)
    (him : Γ ⊩[env] p.imp q) (hp : Δ ⊩[env] p)
    (hq : HasType env [] q .bool)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxpBool : p.freeIn x .bool = false)
    (hxqBool : q.freeIn x .bool = false) :
    (Γ ++ Δ) ⊩[env] q := by
  have hpTy : HasType env [] p .bool := hp.concl_bool
  have hunf := imp_eq_expand x hpTy hq hxpBool
  have him' : Γ ⊩[env] Tm.mkEq .bool (p.and q) p := by
    simpa [Tm.impExpand] using eqMp hunf him
  have hand : (Γ ++ Δ) ⊩[env] p.and q :=
    eqMp (eq_sym him') hp
  exact and_elim_right x hand hpTy hq hxp hxq hxpBool hxqBool

/-- Hypothesis weakening: from `Γ ⊢ p` conclude `q :: Γ ⊢ p`.
The kernel has no structural weakening; this is CONJ + right projection.
`T ∉ q :: Γ` is the usual case (`T` is not an assumption). -/
theorem add_assum {Γ p q} (x : Name)
    (hp : Γ ⊩[env] p) (hq : HasType env [] q .bool)
    (hT : Tm.tru ∉ q :: Γ)
    (hxΓ : ∀ r ∈ Γ, r.freeIn x Tm.boolCombTy = false)
    (hxqComb : q.freeIn x Tm.boolCombTy = false)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxqBool : q.freeIn x .bool = false)
    (hxpBool : p.freeIn x .bool = false) :
    (q :: Γ) ⊩[env] p := by
  have hTq : Tm.tru ∉ [q] := by
    intro ht
    simp at ht
    exact hT (ht ▸ List.Mem.head _)
  have hTΓ : Tm.tru ∉ Γ := fun h => hT (List.Mem.tail _ h)
  have hxq : ∀ r ∈ [q], r.freeIn x Tm.boolCombTy = false := by
    intro r hr
    simp at hr
    exact hr ▸ hxqComb
  have hc := conj x (assume hq) hp hTq hTΓ hxq hxΓ hxqComb hxp hxqBool
  simpa using and_elim_right x hc hq hp.concl_bool hxqComb hxp hxqBool hxpBool

end Provable
end HOLean
