/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Deduction

/-!
# Conservativity of definitional extensions

`Env.addDef n ty rhs` adds the axiom `⊢ n = rhs`.  Every theorem of the
extended environment translates to a theorem of `env` by replacing each
occurrence of `n` with the matching instance of `rhs` (`Tm.unfoldDef`).
In particular, a closed theorem that never mentions `n` is already a
theorem of `env`.

The induction invariant uses *hypothesis inclusion* rather than equality of
hypothesis lists: `unfoldDef` is not injective, so `hypsErase` does not
commute with `List.map (·.unfoldDef …)`.
-/

namespace HOLean

variable {env : Env}

private theorem mem_map_unfoldDef_append {n : Name} {ty : Ty} {rhs : Tm}
    {Γ Δ : List Tm} {q : Tm}
    (h : q ∈ Γ.map (·.unfoldDef n ty rhs) ∨ q ∈ Δ.map (·.unfoldDef n ty rhs)) :
    q ∈ (Γ ++ Δ).map (·.unfoldDef n ty rhs) := by
  simpa [List.map_append, List.mem_append] using h

private theorem mem_map_unfoldDef_hypsErase {n : Name} {ty : Ty} {rhs : Tm}
    {Γ : List Tm} {p q : Tm}
    (hq : q ∈ Γ.map (·.unfoldDef n ty rhs)) (hne : q ≠ p.unfoldDef n ty rhs) :
    q ∈ (hypsErase p Γ).map (·.unfoldDef n ty rhs) := by
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq
  have hq0' : q0 ≠ p := fun heq => hne (by simp [heq])
  exact List.mem_map.2 ⟨q0, by simp [hypsErase, hq0, hq0'], rfl⟩

private theorem Subst_Ok_map_unfoldDef [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (hrhs : HasType env [] rhs ty)
    {σ : Tm.Subst} (hσ : Tm.Subst.Ok (env.addDef n ty rhs) σ) :
    Tm.Subst.Ok env (σ.map fun p => (p.1, p.2.1, p.2.2.unfoldDef n ty rhs)) := by
  intro x α u hu
  have hu' := (Tm.Subst.lookup_map_unfoldDef n ty rhs σ x α).symm.trans hu
  cases hlook : σ.lookup x α with
  | none =>
    simp [hlook] at hu'
  | some u0 =>
    simp [hlook] at hu'
    subst hu'
    exact (hσ x α u0 hlook).unfoldDef hrhs

private theorem exists_unfoldDef_nil {n : Name} {ty : Ty} {rhs : Tm} {p : Tm}
    (h : [] ⊩[env] p.unfoldDef n ty rhs) :
    ∃ Γ', (∀ q ∈ Γ', q ∈ List.map (·.unfoldDef n ty rhs) ([] : List Tm)) ∧
      Γ' ⊩[env] p.unfoldDef n ty rhs :=
  ⟨[], (fun _ hq => nomatch hq), h⟩

/-- Combine two inductive hypotheses whose conclusions are proved under
appended hypothesis lists (`trans` / `mkComb` / `eqMp`). -/
private theorem exists_unfoldDef_append {n : Name} {ty : Ty} {rhs : Tm}
    {Γ Δ : List Tm} {p1 p2 p : Tm}
    (ih1 : ∃ Γ1, (∀ q ∈ Γ1, q ∈ Γ.map (·.unfoldDef n ty rhs)) ∧ Γ1 ⊩[env] p1)
    (ih2 : ∃ Δ1, (∀ q ∈ Δ1, q ∈ Δ.map (·.unfoldDef n ty rhs)) ∧ Δ1 ⊩[env] p2)
    (h : ∀ {Γ1 Δ1}, Γ1 ⊩[env] p1 → Δ1 ⊩[env] p2 →
      Γ1 ++ Δ1 ⊩[env] p.unfoldDef n ty rhs) :
    ∃ Γ', (∀ q ∈ Γ', q ∈ (Γ ++ Δ).map (·.unfoldDef n ty rhs)) ∧
      Γ' ⊩[env] p.unfoldDef n ty rhs :=
  match ih1, ih2 with
  | ⟨Γ1, hΓ1, h1'⟩, ⟨Δ1, hΔ1, h2'⟩ =>
    ⟨Γ1 ++ Δ1, fun q hq =>
      match List.mem_append.1 hq with
      | Or.inl hq1 => mem_map_unfoldDef_append (Or.inl (hΓ1 q hq1))
      | Or.inr hq2 => mem_map_unfoldDef_append (Or.inr (hΔ1 q hq2)),
      h h1' h2'⟩

/-- Translate a deduction across `addDef` by unfolding the new constant.
The resulting hypothesis list is a subset of the unfolded original hypotheses. -/
theorem Provable.unfoldDef [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (hn : env.lookup n = none) (hwf : env.WF)
    (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    {Γ p} (h : Γ ⊩[env.addDef n ty rhs] p) :
    ∃ Γ', (∀ q ∈ Γ', q ∈ Γ.map (·.unfoldDef n ty rhs)) ∧
      Γ' ⊩[env] p.unfoldDef n ty rhs := by
  have hne_eq : n ≠ eqName := Env.HasEq.ne_of_fresh hn
  haveI : Env.HasEq (env.addDef n ty rhs) := Env.HasEq.addDef hne_eq
  have hLC : rhs.LC 0 = true := hrhs.lc0
  induction h with
  | refl ht =>
    apply exists_unfoldDef_nil
    rw [Tm.unfoldDef_mkEq n ty rhs _ _ _ hne_eq]
    exact Provable.refl (ht.unfoldDef hrhs)
  | @trans Γ Δ s t u α _ _ ih1 ih2 =>
    refine exists_unfoldDef_append ih1 ih2 fun h1' h2' => ?_
    rw [Tm.unfoldDef_mkEq n ty rhs α _ _ hne_eq] at h1' h2' ⊢
    exact Provable.trans h1' h2'
  | @mkComb Γ Δ f g x y α β _ _ ih1 ih2 =>
    refine exists_unfoldDef_append ih1 ih2 fun h1' h2' => ?_
    rw [Tm.unfoldDef_mkEq n ty rhs (α ↝ β) _ _ hne_eq] at h1'
    rw [Tm.unfoldDef_mkEq n ty rhs α _ _ hne_eq] at h2'
    rw [Tm.unfoldDef_mkEq n ty rhs β _ _ hne_eq]
    simpa [Tm.unfoldDef] using Provable.mkComb h1' h2'
  | @abs Γ s t x α β _ hfresh ih =>
    obtain ⟨Γ1, hΓ1, h1'⟩ := ih
    refine ⟨Γ1, hΓ1, ?_⟩
    rw [Tm.unfoldDef_mkEq n ty rhs β _ _ hne_eq] at h1'
    rw [Tm.unfoldDef_mkEq n ty rhs (α ↝ β) _ _ hne_eq]
    simp only [Tm.unfoldDef_abstract n ty rhs _ x α hclosed] at h1' ⊢
    refine Provable.abs h1' ?_
    intro r hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 (hΓ1 r hr)
    simpa [Tm.unfoldDef_freeIn n ty rhs r0 hclosed] using hfresh r0 hr0
  | @beta t x α β ht =>
    apply exists_unfoldDef_nil
    rw [Tm.unfoldDef_mkEq n ty rhs β _ _ hne_eq]
    simp only [Tm.unfoldDef, Tm.unfoldDef_open' n ty rhs _ _ hclosed hLC]
    exact Provable.beta (ht.unfoldDef hrhs)
  | @assume p hp =>
    refine ⟨[p.unfoldDef n ty rhs], ?_, Provable.assume (hp.unfoldDef hrhs)⟩
    · intro q hq
      simp at hq
      exact List.mem_map.2 ⟨p, List.Mem.head _, hq.symm⟩
  | @eqMp Γ Δ p q _ _ ih1 ih2 =>
    refine exists_unfoldDef_append ih1 ih2 fun h1' h2' => ?_
    rw [Tm.unfoldDef_mkEq n ty rhs .bool _ _ hne_eq] at h1'
    exact Provable.eqMp h1' h2'
  | @deductAntisym Γ Δ p q _ _ ih1 ih2 =>
    obtain ⟨Γ1, hΓ1, h1'⟩ := ih1
    obtain ⟨Δ1, hΔ1, h2'⟩ := ih2
    refine ⟨hypsErase (q.unfoldDef n ty rhs) Γ1 ++
        hypsErase (p.unfoldDef n ty rhs) Δ1, ?_, ?_⟩
    · intro r hr
      match List.mem_append.1 hr with
      | Or.inl hr1 =>
        have hr1' : r ∈ Γ1 ∧ r ≠ q.unfoldDef n ty rhs := by simpa [hypsErase] using hr1
        exact mem_map_unfoldDef_append
          (Or.inl (mem_map_unfoldDef_hypsErase (hΓ1 r hr1'.1) hr1'.2))
      | Or.inr hr2 =>
        have hr2' : r ∈ Δ1 ∧ r ≠ p.unfoldDef n ty rhs := by simpa [hypsErase] using hr2
        exact mem_map_unfoldDef_append
          (Or.inr (mem_map_unfoldDef_hypsErase (hΔ1 r hr2'.1) hr2'.2))
    · rw [Tm.unfoldDef_mkEq n ty rhs .bool _ _ hne_eq]
      exact Provable.deductAntisym h1' h2'
  | @instType Γ p θ h ih =>
    obtain ⟨Γ1, hΓ1, h1'⟩ := ih
    have hbool := Provable.bool_typed h
    refine ⟨Γ1.map (·.instTy θ), ?_, ?_⟩
    · intro q hq
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.1 hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 (hΓ1 q1 hq1)
      have hcomm :=
        (hbool.1 q0 hq0).unfoldDef_instTy (n := n) (ty := ty) (rhs := rhs) θ hvars
      refine List.mem_map.2 ⟨q0.instTy θ, List.mem_map.2 ⟨q0, hq0, rfl⟩, ?_⟩
      exact hcomm
    · have hcomm :=
        hbool.2.unfoldDef_instTy (n := n) (ty := ty) (rhs := rhs) θ hvars
      rw [hcomm]
      exact Provable.instType θ h1'
  | @inst Γ p σ hσ h ih =>
    obtain ⟨Γ1, hΓ1, h1'⟩ := ih
    let σ' : Tm.Subst := σ.map fun p => (p.1, p.2.1, p.2.2.unfoldDef n ty rhs)
    have hσ' : Tm.Subst.Ok env σ' := Subst_Ok_map_unfoldDef n hrhs hσ
    refine ⟨Γ1.map (·.applySubst σ'), ?_, ?_⟩
    · intro q hq
      obtain ⟨q1, hq1, rfl⟩ := List.mem_map.1 hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 (hΓ1 q1 hq1)
      have hcomm := Tm.unfoldDef_applySubst n ty rhs q0 σ hclosed
      refine List.mem_map.2 ⟨q0.applySubst σ, List.mem_map.2 ⟨q0, hq0, rfl⟩, ?_⟩
      exact hcomm
    · have hcomm := Tm.unfoldDef_applySubst n ty rhs p σ hclosed
      rw [hcomm]
      exact Provable.inst (σ := σ') hσ' h1'
  | ax hp hty =>
    cases hp with
    | head =>
      apply exists_unfoldDef_nil
      rw [Tm.unfoldDef_mkEq n ty rhs ty _ _ hne_eq,
        Tm.unfoldDef_const_generic n ty rhs hvars,
        Tm.unfoldDef_of_not_hasConst n ty rhs rhs
          (hrhs.not_hasConst_of_fresh hn)]
      exact Provable.refl hrhs
    | tail _ hold =>
      apply exists_unfoldDef_nil
      have hfresh := (hwf _ hold).not_hasConst_of_fresh hn
      rw [Tm.unfoldDef_of_not_hasConst n ty rhs _ hfresh]
      exact Provable.ax hold (hwf _ hold)

/-- Closed theorems that avoid the new name are already theorems of `env`. -/
theorem Provable.addDef_conservative [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (hn : env.lookup n = none) (hwf : env.WF)
    (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    {p} (h : [] ⊩[env.addDef n ty rhs] p) (hp : p.hasConst n = false) :
    [] ⊩[env] p := by
  obtain ⟨Γ', hΓ', h'⟩ := Provable.unfoldDef n hn hwf hrhs hclosed hvars h
  have hΓ'' : Γ' = [] := by
    cases Γ' with
    | nil => rfl
    | cons q qs =>
      have := hΓ' q (List.Mem.head _)
      simp at this
  subst hΓ''
  rwa [Tm.unfoldDef_of_not_hasConst n ty rhs p hp] at h'

/-- Closed theorems that avoid the new name are provable in the extended
environment if and only if they are provable in the base environment. -/
theorem Provable.addDef_iff [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (hn : env.lookup n = none) (hwf : env.WF)
    (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    {p} (hp : p.hasConst n = false) :
    [] ⊩[env.addDef n ty rhs] p ↔ [] ⊩[env] p :=
  Iff.intro
    (fun h => Provable.addDef_conservative n hn hwf hrhs hclosed hvars h hp)
    (Provable.weakenEnv (Env.LE.addDef_of_fresh hn))

/-- Relative consistency: a definitional extension cannot prove a false
unless the base environment already could. -/
theorem Provable.addDef_consistent [Env.HasEq env] (n : Name) {ty : Ty} {rhs : Tm}
    (hn : env.lookup n = none) (hwf : env.WF)
    (hrhs : HasType env [] rhs ty)
    (hclosed : ∀ x α, rhs.freeIn x α = false)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)
    {p} (hp : p.hasConst n = false)
    (hcons : ¬ [] ⊩[env] p) :
    ¬ [] ⊩[env.addDef n ty rhs] p :=
  fun h => hcons (Provable.addDef_conservative n hn hwf hrhs hclosed hvars h hp)

end HOLean
