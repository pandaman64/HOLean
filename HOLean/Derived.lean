/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Connective
import HOLean.Kernel

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

namespace Provable

theorem tru_intro : [] ⊩ Tm.tru :=
  refl (HasType.lam (HasType.bvar (by simp [Ctx.get])))

theorem eq_sym {Γ s t α} (h : Γ ⊩ Tm.mkEq α s t) : Γ ⊩ Tm.mkEq α t s := by
  obtain ⟨_, hs, _ht⟩ := HasType.dest_mkEq h.concl_bool
  have hrefl_eq : [] ⊩ Tm.mkEq (α ↝ α ↝ .bool) (Tm.const .eq α) (Tm.const .eq α) :=
    refl (HasType.const .eq α)
  have hfun : Γ ⊩ Tm.mkEq (α ↝ .bool) ((Tm.const .eq α).app s) ((Tm.const .eq α).app t) := by
    simpa using mkComb hrefl_eq h
  have hrefl_s : [] ⊩ Tm.mkEq α s s := refl hs
  have hboolEq : Γ ⊩ Tm.mkEq .bool (Tm.mkEq α s s) (Tm.mkEq α t s) := by
    simpa [Tm.mkEq] using mkComb hfun hrefl_s
  simpa [Tm.mkEq] using eqMp hboolEq hrefl_s

theorem eqt_intro {Γ p} (h : Γ ⊩ p) :
    hypsErase Tm.tru Γ ⊩ Tm.mkEq .bool p Tm.tru := by
  simpa [hypsErase] using deductAntisym h tru_intro

theorem gen {Γ t x α} (h : Γ ⊩ t)
    (hfresh : ∀ r ∈ Γ, r.freeIn x α = false) :
    hypsErase Tm.tru Γ ⊩ Tm.all α (t.abstract x α) := by
  have hT : Tm.tru.freeIn x α = false := Tm.tru_not_free x α
  have hfresh' : ∀ r ∈ hypsErase Tm.tru Γ, r.freeIn x α = false := by
    intro r hr
    have : r ∈ Γ ∧ r ≠ Tm.tru := by simpa [hypsErase] using hr
    exact hfresh r this.1
  have habs := abs (eqt_intro h) hfresh'
  have htruAbs : Tm.tru.abstract x α = Tm.lam α Tm.tru := by
    simp [Tm.abstract, Tm.close, Tm.closeAt_fresh (t := Tm.tru) hT]
  simpa [Tm.all, htruAbs] using habs

theorem beta_conv {t u : Tm} {x : Name} {α β : Ty}
    (ht : HasType [α] t β) (hu : HasType [] u α)
    (hf : t.freeIn x α = false) :
    [] ⊩ Tm.mkEq β ((Tm.lam α t).app u) (t.open' u) := by
  have hβ := beta (t := t) (x := x) (α := α) (β := β) ht
  have hσ : Tm.Subst.Ok [(x, α, u)] := by
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

theorem conj {Γ Δ p q : _} (x : Name)
    (hp : Γ ⊩ p) (hq : Δ ⊩ q)
    (hxΓ : ∀ r ∈ hypsErase Tm.tru Γ, r.freeIn x Tm.boolCombTy = false)
    (hxΔ : ∀ r ∈ hypsErase Tm.tru Δ, r.freeIn x Tm.boolCombTy = false)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false) :
    (hypsErase Tm.tru Γ ++ hypsErase Tm.tru Δ) ⊩ p.and q := by
  have hpT := eqt_intro hp
  have hqT := eqt_intro hq
  have hp0 : p.LC 0 = true := hp.concl_bool.lc0
  have hq0 : q.LC 0 = true := hq.concl_bool.lc0
  have hT0 : Tm.tru.LC 0 = true := Tm.tru_LC
  have hf : [] ⊩ Tm.mkEq Tm.boolCombTy (Tm.fvar x Tm.boolCombTy) (Tm.fvar x Tm.boolCombTy) :=
    refl (HasType.fvar x Tm.boolCombTy)
  have h1 := mkComb hf hpT
  have h2 := mkComb h1 hqT
  have hfresh : ∀ r ∈ hypsErase Tm.tru Γ ++ hypsErase Tm.tru Δ,
      r.freeIn x Tm.boolCombTy = false := by
    intro r hr
    match List.mem_append.1 hr with
    | Or.inl hr => exact hxΓ r hr
    | Or.inr hr => exact hxΔ r hr
  have h2' :
      hypsErase Tm.tru Γ ++ hypsErase Tm.tru Δ ⊩
        Tm.mkEq .bool
          (((Tm.fvar x Tm.boolCombTy).app p).app q)
          (((Tm.fvar x Tm.boolCombTy).app Tm.tru).app Tm.tru) := by
    simpa using h2
  have habs := abs h2' hfresh
  have hpq := Tm.abstract_app_app_fvar x Tm.boolCombTy p q hxp hxq
  have hTT :=
    Tm.abstract_app_app_fvar x Tm.boolCombTy Tm.tru Tm.tru
      (Tm.tru_not_free _ _) (Tm.tru_not_free _ _)
  have hand :
      p.and q =
        Tm.mkEq (Tm.boolCombTy ↝ .bool)
          ((((Tm.fvar x Tm.boolCombTy).app p).app q).abstract x Tm.boolCombTy)
          ((((Tm.fvar x Tm.boolCombTy).app Tm.tru).app Tm.tru).abstract x Tm.boolCombTy) := by
    unfold Tm.and
    simp only [Tm.shift_of_LC0 hp0, Tm.shift_of_LC0 hq0, Tm.shift_of_LC0 hT0]
    rw [← hpq, ← hTT]
  exact hand ▸ habs

def projSnd : Tm :=
  Tm.lam .bool (Tm.lam .bool (Tm.bvar 0))

def projFst : Tm :=
  Tm.lam .bool (Tm.lam .bool (Tm.bvar 1))

theorem hasType_projSnd : HasType [] projSnd Tm.boolCombTy :=
  HasType.lam (HasType.lam (HasType.bvar (by simp [Ctx.get])))

theorem hasType_projFst : HasType [] projFst Tm.boolCombTy :=
  HasType.lam (HasType.lam (HasType.bvar (by simp [Ctx.get])))

theorem and_lhs_type {p q} (hp : HasType [] p .bool) (hq : HasType [] q .bool) :
    HasType [Tm.boolCombTy] (((Tm.bvar 0).app p).app q) .bool := by
  unfold Tm.boolCombTy
  exact HasType.app (HasType.app (HasType.bvar (by simp [Ctx.get])) hp.of_closed) hq.of_closed

theorem and_rhs_type :
    HasType [Tm.boolCombTy] (((Tm.bvar 0).app Tm.tru).app Tm.tru) .bool := by
  unfold Tm.boolCombTy
  exact HasType.app (HasType.app (HasType.bvar (by simp [Ctx.get])) HasType.tru) HasType.tru

theorem and_eq_combinators {p q}
    (hp : HasType [] p .bool) (hq : HasType [] q .bool) :
    p.and q =
      Tm.mkEq (Tm.boolCombTy ↝ .bool)
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q))
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)) := by
  simp [Tm.and, Tm.shift_of_LC0 hp.lc0, Tm.shift_of_LC0 hq.lc0, Tm.shift_of_LC0 Tm.tru_LC]

/-- `(λ f. f p q) u = u p q` by general β. -/
theorem comb_beta {p q u : Tm} (x : Name)
    (hp : HasType [] p .bool) (hq : HasType [] q .bool)
    (hu : HasType [] u Tm.boolCombTy)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false) :
    [] ⊩ Tm.mkEq .bool
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
    (hp : HasType [] p .bool) (hq : HasType [] q .bool)
    (hxp : p.freeIn x .bool = false) :
    [] ⊩ Tm.mkEq .bool ((projFst.app p).app q) p := by
  have ht : HasType [.bool] (Tm.lam .bool (Tm.bvar 1)) (.bool ↝ .bool) :=
    HasType.lam (HasType.bvar (by simp [Ctx.get]))
  have h1 :=
    beta_conv (t := Tm.lam .bool (Tm.bvar 1)) (u := p) (x := x)
      (α := .bool) (β := .bool ↝ .bool) ht hp (by simp [Tm.freeIn])
  have h1' : [] ⊩ Tm.mkEq (.bool ↝ .bool) (projFst.app p) (Tm.lam .bool p) := by
    simpa [projFst, Tm.open', Tm.openAt] using h1
  have h2 : [] ⊩ Tm.mkEq .bool ((projFst.app p).app q) ((Tm.lam .bool p).app q) := by
    simpa using mkComb h1' (refl hq)
  have h3 :=
    beta_conv (t := p) (u := q) (x := x) (α := .bool) (β := .bool)
      hp.of_closed hq hxp
  have h3' : [] ⊩ Tm.mkEq .bool ((Tm.lam .bool p).app q) p := by
    simpa [Tm.openAt_of_LC hp.lc0] using h3
  simpa using trans h2 h3'

theorem projSnd_beta {p q : Tm} (x : Name)
    (hp : HasType [] p .bool) (hq : HasType [] q .bool)
    (_hxq : q.freeIn x .bool = false) :
    [] ⊩ Tm.mkEq .bool ((projSnd.app p).app q) q := by
  have ht : HasType [.bool] (Tm.lam .bool (Tm.bvar 0)) (.bool ↝ .bool) :=
    HasType.lam (HasType.bvar (by simp [Ctx.get]))
  have h1 :=
    beta_conv (t := Tm.lam .bool (Tm.bvar 0)) (u := p) (x := x)
      (α := .bool) (β := .bool ↝ .bool) ht hp (by simp [Tm.freeIn])
  have h1' : [] ⊩ Tm.mkEq (.bool ↝ .bool) (projSnd.app p) (Tm.lam .bool (Tm.bvar 0)) := by
    simpa [projSnd, Tm.open', Tm.openAt] using h1
  have h2 : [] ⊩ Tm.mkEq .bool ((projSnd.app p).app q) ((Tm.lam .bool (Tm.bvar 0)).app q) := by
    simpa using mkComb h1' (refl hq)
  have h3 :=
    beta_conv (t := Tm.bvar 0) (u := q) (x := x) (α := .bool) (β := .bool)
      (HasType.bvar (by simp [Ctx.get])) hq (by simp [Tm.freeIn])
  have h3' : [] ⊩ Tm.mkEq .bool ((Tm.lam .bool (Tm.bvar 0)).app q) q := by
    simpa [Tm.open', Tm.openAt] using h3
  simpa using trans h2 h3'

/-- Left projection: `Γ ⊢ p ∧ q` gives `Γ ⊢ p`. -/
theorem and_elim_left {Γ p q} (x : Name)
    (h : Γ ⊩ p.and q)
    (hp : HasType [] p .bool) (hq : HasType [] q .bool)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxpBool : p.freeIn x .bool = false) :
    Γ ⊩ p := by
  have heq :
      Γ ⊩ Tm.mkEq (Tm.boolCombTy ↝ .bool)
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q))
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)) :=
    (and_eq_combinators hp hq) ▸ h
  have happ :
      Γ ⊩ Tm.mkEq .bool
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projFst)
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projFst) := by
    simpa using mkComb heq (refl hasType_projFst)
  have hl := comb_beta (p := p) (q := q) (u := projFst) x hp hq hasType_projFst hxp hxq
  have hr :=
    comb_beta (p := Tm.tru) (q := Tm.tru) (u := projFst) x
      HasType.tru HasType.tru hasType_projFst
      (Tm.tru_not_free _ _) (Tm.tru_not_free _ _)
  have hπp := projFst_beta x hp hq hxpBool
  have hπT := projFst_beta (p := Tm.tru) (q := Tm.tru) x HasType.tru HasType.tru
    (Tm.tru_not_free x .bool)
  have hl' : [] ⊩ Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projFst) p :=
    trans hl hπp
  have hr' : [] ⊩ Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projFst) Tm.tru :=
    trans hr hπT
  have hpT : Γ ⊩ Tm.mkEq .bool p Tm.tru := by
    have h1 := trans (eq_sym hl') happ
    simpa using trans h1 hr'
  simpa using eqMp (eq_sym hpT) tru_intro

/-- Right projection: `Γ ⊢ p ∧ q` gives `Γ ⊢ q`. -/
theorem and_elim_right {Γ p q} (x : Name)
    (h : Γ ⊩ p.and q)
    (hp : HasType [] p .bool) (hq : HasType [] q .bool)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxqBool : q.freeIn x .bool = false) :
    Γ ⊩ q := by
  have heq :
      Γ ⊩ Tm.mkEq (Tm.boolCombTy ↝ .bool)
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q))
        (Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)) :=
    (and_eq_combinators hp hq) ▸ h
  have happ :
      Γ ⊩ Tm.mkEq .bool
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projSnd)
        ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projSnd) := by
    simpa using mkComb heq (refl hasType_projSnd)
  have hl := comb_beta (p := p) (q := q) (u := projSnd) x hp hq hasType_projSnd hxp hxq
  have hr :=
    comb_beta (p := Tm.tru) (q := Tm.tru) (u := projSnd) x
      HasType.tru HasType.tru hasType_projSnd
      (Tm.tru_not_free _ _) (Tm.tru_not_free _ _)
  have hπq := projSnd_beta x hp hq hxqBool
  have hπT := projSnd_beta (p := Tm.tru) (q := Tm.tru) x HasType.tru HasType.tru
    (Tm.tru_not_free x .bool)
  have hl' : [] ⊩ Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app p).app q)).app projSnd) q :=
    trans hl hπq
  have hr' : [] ⊩ Tm.mkEq .bool
      ((Tm.lam Tm.boolCombTy (((Tm.bvar 0).app Tm.tru).app Tm.tru)).app projSnd) Tm.tru :=
    trans hr hπT
  have hqT : Γ ⊩ Tm.mkEq .bool q Tm.tru := by
    have h1 := trans (eq_sym hl') happ
    simpa using trans h1 hr'
  simpa using eqMp (eq_sym hqT) tru_intro

/-- Modus ponens from `p ⇒ q ≔ (p ∧ q) = p`. -/
theorem mp {Γ Δ p q} (x : Name)
    (him : Γ ⊩ p.imp q) (hp : Δ ⊩ p)
    (hq : HasType [] q .bool)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxq : q.freeIn x Tm.boolCombTy = false)
    (hxqBool : q.freeIn x .bool = false) :
    (Γ ++ Δ) ⊩ q := by
  have hpTy : HasType [] p .bool := hp.concl_bool
  have him' : Γ ⊩ Tm.mkEq .bool (p.and q) p := by
    simpa [Tm.imp] using him
  have hand : (Γ ++ Δ) ⊩ p.and q :=
    eqMp (eq_sym him') hp
  exact and_elim_right x hand hpTy hq hxp hxq hxqBool

/-- Hypothesis weakening: from `Γ ⊢ p` conclude `q, Γ ⊢ p`.
The kernel has no structural weakening; this is CONJ + right projection. -/
theorem add_assum {Γ p q} (x : Name)
    (hp : Γ ⊩ p) (hq : HasType [] q .bool)
    (hxΓ : ∀ r ∈ hypsErase Tm.tru Γ, r.freeIn x Tm.boolCombTy = false)
    (hxqComb : q.freeIn x Tm.boolCombTy = false)
    (hxp : p.freeIn x Tm.boolCombTy = false)
    (hxpBool : p.freeIn x .bool = false) :
    (hypsErase Tm.tru [q] ++ hypsErase Tm.tru Γ) ⊩ p := by
  have hxq : ∀ r ∈ hypsErase Tm.tru [q], r.freeIn x Tm.boolCombTy = false := by
    intro r hr
    have : r ∈ [q] ∧ r ≠ Tm.tru := by simpa [hypsErase] using hr
    simp at this
    exact this.1 ▸ hxqComb
  have hc := conj x (assume hq) hp hxq hxΓ hxqComb hxp
  exact and_elim_right x hc hq hp.concl_bool hxqComb hxp hxpBool

end Provable
end HOLean
