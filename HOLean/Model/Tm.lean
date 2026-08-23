/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Model.Const
import HOLean.Typing

/-!
# Term interpretation

A well-typed term is interpreted as an element of `α.denote ρ`.  The
function itself is defined by recursion on the raw term (so it lands in
`Type`); `HasType.denote_mem` then shows that a typing derivation puts
the result in the right universe.
-/

open ZFSet Classical

namespace HOLean

/-- Bound-variable assignment: `vals[i]` inhabits `Γ[i]`. -/
structure CtxVal (ρ : TyVal) (Γ : List Ty) where
  vals : List ZFSet
  length_eq : vals.length = Γ.length
  typed : ∀ (i : Nat) (hi : i < Γ.length),
    vals[i]'(length_eq ▸ hi) ∈ (Γ[i]'hi).denote ρ

def CtxVal.nil (ρ : TyVal) : CtxVal ρ [] :=
  ⟨[], rfl, fun _i hi => nomatch hi⟩

@[simp] theorem CtxVal.nil_vals (ρ : TyVal) : (CtxVal.nil ρ).vals = [] := rfl

def CtxVal.cons {ρ : TyVal} {α : Ty} {Γ : List Ty}
    (vs : CtxVal ρ Γ) (x : ZFSet) (hx : x ∈ α.denote ρ) :
    CtxVal ρ (α :: Γ) where
  vals := x :: vs.vals
  length_eq := by simp [vs.length_eq]
  typed := by
    intro i hi
    cases i with
    | zero =>
      simpa [List.getElem_cons_zero] using hx
    | succ n =>
      simpa [List.getElem_cons_succ] using vs.typed n (Nat.lt_of_succ_lt_succ hi)

def CtxVal.get {ρ : TyVal} {Γ : List Ty} (vs : CtxVal ρ Γ)
    {i : Nat} {α : Ty} (h : Γ[i]? = some α) : ZFSet :=
  have hi : i < Γ.length := (List.getElem?_eq_some_iff.1 h).1
  vs.vals[i]'(vs.length_eq ▸ hi)

theorem CtxVal.get_mem {ρ : TyVal} {Γ : List Ty} (vs : CtxVal ρ Γ)
    {i : Nat} {α : Ty} (h : Γ[i]? = some α) :
    vs.get h ∈ α.denote ρ := by
  obtain ⟨hi, hΓ⟩ := List.getElem?_eq_some_iff.1 h
  simpa [CtxVal.get, hΓ] using vs.typed i hi

theorem CtxVal.getElem?_get {ρ : TyVal} {Γ : List Ty} (vs : CtxVal ρ Γ)
    {i : Nat} {α : Ty} (h : Γ[i]? = some α) :
    vs.vals[i]? = some (vs.get h) := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.1 h
  simp [CtxVal.get, vs.length_eq, hi]

/-- Free-variable assignment: every HOL pair `(x, α)` inhabits `⟦α⟧`. -/
structure FVarVal (ρ : TyVal) where
  val : Name → Ty → ZFSet
  mem : ∀ x α, val x α ∈ α.denote ρ

noncomputable def FVarVal.ofNonempty {ρ : TyVal} (hρ : ρ.Nonempty) : FVarVal ρ where
  val := fun _ α => Classical.choose (Ty.denote_nonempty hρ α)
  mem := fun _ α => Classical.choose_spec (Ty.denote_nonempty hρ α)

/-- Interpretation of the constant table: each well-typed occurrence
`const n inst` is an element of `⟦inst⟧`. -/
structure EnvInterp (env : Env) (ρ : TyVal) where
  interp : Name → Ty → ZFSet
  mem : ∀ {n inst gen},
    env.constants n = some gen →
    gen.isInstanceOf inst →
    interp n inst ∈ inst.denote ρ

/-- Pointwise body of a λ-graph: apply `g` on the domain, dummy off it. -/
noncomputable def lamFn {ρ : TyVal} {γ : Ty}
    (g : (x : ZFSet) → x ∈ γ.denote ρ → ZFSet) (x : ZFSet) : ZFSet :=
  if hx : x ∈ γ.denote ρ then g x hx else ∅

noncomputable instance {ρ : TyVal} {γ : Ty}
    (g : (x : ZFSet) → x ∈ γ.denote ρ → ZFSet) :
    Definable₁ (lamFn (ρ := ρ) (γ := γ) g) :=
  Classical.allZFSetDefinable _

theorem lamFn_isFunc {ρ : TyVal} {γ β : Ty}
    (g : (x : ZFSet) → x ∈ γ.denote ρ → ZFSet)
    (hg : ∀ x hx, g x hx ∈ β.denote ρ) :
    IsFunc (γ.denote ρ) (β.denote ρ) (map (lamFn (ρ := ρ) (γ := γ) g) (γ.denote ρ)) :=
  (map_isFunc (f := lamFn (ρ := ρ) (γ := γ) g)
    (x := γ.denote ρ) (y := β.denote ρ)).mpr fun x hx => by
    simpa [lamFn, hx] using hg x hx

/-- Graph of a HOL term under an environment interpretation. -/
noncomputable def Tm.denote {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) (vs : List ZFSet) : Tm → ZFSet
  | .bvar i => vs[i]?.getD ∅
  | .fvar x α => ξ.val x α
  | .const n inst => I.interp n inst
  | .app f a => zfApp (f.denote I ξ vs) (a.denote I ξ vs)
  | .lam α t =>
    map (lamFn (ρ := ρ) (γ := α) fun x _hx => t.denote I ξ (x :: vs))
      (α.denote ρ)

/-- Graph of a typed term, using the bound-variable assignment in `vs`. -/
noncomputable def HasType.denote {env : Env} {ρ : TyVal} {Γ t α}
    (_h : HasType env Γ t α) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : CtxVal ρ Γ) : ZFSet :=
  t.denote I ξ vs.vals

/-- The denotation of a typed term lands in the denotation of its type. -/
theorem HasType.denote_mem {env : Env} {ρ : TyVal} {Γ tm σ}
    (h : HasType env Γ tm σ) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : CtxVal ρ Γ) :
    h.denote I ξ vs ∈ σ.denote ρ := by
  induction h with
  | bvar hi =>
    simp [HasType.denote, Tm.denote, vs.getElem?_get hi]
    exact vs.get_mem hi
  | fvar x α =>
    simpa [HasType.denote, Tm.denote] using ξ.mem x α
  | const hconst hinst =>
    simpa [HasType.denote, Tm.denote] using I.mem hconst hinst
  | app hf ha ihf iha =>
    have hfI := mem_funs.1 (by simpa [HasType.denote, Ty.denote_arrow] using ihf vs)
    simpa [HasType.denote, Tm.denote] using
      (zfApp_spec hfI (by simpa [HasType.denote] using iha vs)).2
  | lam ht ih =>
    simp only [HasType.denote, Tm.denote]
    apply mem_funs.2
    apply lamFn_isFunc
    intro x hx
    simpa [HasType.denote, CtxVal.cons] using ih (vs.cons x hx)

/-- Applying the graph of a λ recovers the interpretation of the body. -/
theorem HasType.denote_lam_app {env : Env} {ρ : TyVal} {Γ} {γ β : Ty} {t : Tm}
    (ht : HasType env (γ :: Γ) t β) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : CtxVal ρ Γ) {x : ZFSet} (hx : x ∈ γ.denote ρ) :
    zfApp ((HasType.lam ht).denote I ξ vs) x = ht.denote I ξ (vs.cons x hx) := by
  let g := fun (y : ZFSet) (_hy : y ∈ γ.denote ρ) => t.denote I ξ (y :: vs.vals)
  have hf := lamFn_isFunc (ρ := ρ) (γ := γ) (β := β) g fun y hy =>
    (by
      have := ht.denote_mem I ξ (vs.cons y hy)
      simpa [HasType.denote, CtxVal.cons] using this)
  have hpair : pair x (lamFn (ρ := ρ) (γ := γ) g x) ∈
      map (lamFn (ρ := ρ) (γ := γ) g) (γ.denote ρ) :=
    mem_map.2 ⟨x, hx, rfl⟩
  have hfx : lamFn (ρ := ρ) (γ := γ) g x = t.denote I ξ (x :: vs.vals) := by
    simp [lamFn, g, hx]
  simpa [HasType.denote, Tm.denote, CtxVal.cons, hfx] using
    zfApp_unique hf hx hpair

/-- Same fact, stated on raw terms so later truth-table proofs avoid
unfolding the opaque `HasType.denote`. -/
theorem Tm.denote_of_lam_app {env : Env} {ρ : TyVal} {Γ} {γ β : Ty} {t : Tm}
    (ht : HasType env (γ :: Γ) t β) (I : EnvInterp env ρ) (ξ : FVarVal ρ)
    (vs : CtxVal ρ Γ) {x : ZFSet} (hx : x ∈ γ.denote ρ) :
    zfApp ((Tm.lam γ t).denote I ξ vs.vals) x = t.denote I ξ (x :: vs.vals) :=
  HasType.denote_lam_app ht I ξ vs hx

@[simp] theorem Tm.denote_bvar_zero {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) (x : ZFSet) (vs : List ZFSet) :
    (Tm.bvar 0).denote I ξ (x :: vs) = x :=
  rfl

@[simp] theorem Tm.denote_bvar_one {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) (x y : ZFSet) (vs : List ZFSet) :
    (Tm.bvar 1).denote I ξ (x :: y :: vs) = y :=
  rfl

@[simp] theorem Tm.denote_bvar_two {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (ξ : FVarVal ρ) (x y z : ZFSet) (vs : List ZFSet) :
    (Tm.bvar 2).denote I ξ (x :: y :: z :: vs) = z :=
  rfl

/-- Interpretation of `eq` at an instantiated type. -/
noncomputable def interpEq (ρ : TyVal) (inst : Ty) : ZFSet :=
  match inst with
  | .arrow α (.arrow β .bool) =>
    if α = β then zfEq (α.denote ρ) else ∅
  | _ => ∅

/-- Interpretation of `select` at an instantiated type. -/
noncomputable def interpSelect (ρ : TyVal) (hρ : ρ.Nonempty) (inst : Ty) : ZFSet :=
  match inst with
  | .arrow (.arrow α .bool) β =>
    if α = β then zfSelect (α.denote ρ) (Ty.denote_nonempty hρ α) else ∅
  | _ => ∅

theorem interpEq_mem {ρ : TyVal} {inst : Ty}
    (h : eqTy.isInstanceOf inst) :
    interpEq ρ inst ∈ inst.denote ρ := by
  obtain ⟨α, rfl⟩ := eqTy_isInstanceOf_iff.1 h
  simp [interpEq]
  exact zfEq_isFunc (α.denote ρ)

theorem interpSelect_mem {ρ : TyVal} {inst : Ty} (hρ : ρ.Nonempty)
    (h : selectTy.isInstanceOf inst) :
    interpSelect ρ hρ inst ∈ inst.denote ρ := by
  obtain ⟨α, rfl⟩ := selectTy_isInstanceOf_iff.1 h
  simp [interpSelect]
  exact zfSelect_isFunc (α.denote ρ) (Ty.denote_nonempty hρ α)

/-- `holCore` interpreted by the equality and choice graphs. -/
noncomputable def EnvInterp.holCore (ρ : TyVal) (hρ : ρ.Nonempty) :
    EnvInterp holCore ρ where
  interp n inst :=
    if n = eqName then interpEq ρ inst
    else if n = selectName then interpSelect ρ hρ inst
    else ∅
  mem := by
    intro n inst gen hconst hinst
    simp [holCore_constants] at hconst
    by_cases heq : n = eqName
    · subst heq
      simp [holConstants] at hconst
      cases hconst
      simpa using interpEq_mem (ρ := ρ) hinst
    · by_cases hsel : n = selectName
      · subst hsel
        rw [holConstants_select] at hconst
        cases hconst
        simpa [heq] using interpSelect_mem (ρ := ρ) hρ hinst
      · rw [holConstants_of_ne heq hsel] at hconst
        cases hconst

theorem EnvInterp.holCore_interp_eq (ρ : TyVal) (hρ : ρ.Nonempty) (α : Ty) :
    (EnvInterp.holCore ρ hρ).interp eqName (α ↝ α ↝ .bool) =
      zfEq (α.denote ρ) := by
  simp [EnvInterp.holCore, interpEq]

theorem EnvInterp.holCore_interp_select (ρ : TyVal) (hρ : ρ.Nonempty) (α : Ty) :
    (EnvInterp.holCore ρ hρ).interp selectName ((α ↝ .bool) ↝ α) =
      zfSelect (α.denote ρ) (Ty.denote_nonempty hρ α) := by
  simp [EnvInterp.holCore, interpSelect, eqName_ne_selectName.symm]

/-- Update one HOL free variable. -/
noncomputable def FVarVal.update {ρ : TyVal} (ξ : FVarVal ρ)
    (x : Name) (α : Ty) (v : ZFSet) (hv : v ∈ α.denote ρ) : FVarVal ρ where
  val y β := if y = x ∧ β = α then v else ξ.val y β
  mem y β := by
    by_cases h : y = x ∧ β = α
    · simp [h]
      exact h.2 ▸ hv
    · simp [h]
      exact ξ.mem y β

theorem FVarVal.update_self {ρ : TyVal} (ξ : FVarVal ρ)
    {x α v} (hv : v ∈ α.denote ρ) :
    (ξ.update x α v hv).val x α = v := by
  simp [FVarVal.update]

theorem FVarVal.update_of_ne {ρ : TyVal} (ξ : FVarVal ρ)
    {x α v} (hv : v ∈ α.denote ρ) {y β}
    (h : ¬ (y = x ∧ β = α)) :
    (ξ.update x α v hv).val y β = ξ.val y β := by
  simp [FVarVal.update, h]

/-- Reindex a free-variable assignment along a type substitution. -/
noncomputable def FVarVal.pull {ρ : TyVal} (ξ : FVarVal ρ) (θ : TySubst) :
    FVarVal (ρ.inst θ) where
  val x α := ξ.val x (α.inst θ)
  mem x α := by
    simpa [Ty.denote_inst] using ξ.mem x (α.inst θ)

/-- Push an environment interpretation through a type substitution. -/
noncomputable def EnvInterp.inst {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (θ : TySubst) : EnvInterp env (ρ.inst θ) where
  interp n α := I.interp n (α.inst θ)
  mem := by
    intro n inst gen hconst hinst
    simpa [Ty.denote_inst] using I.mem hconst (hinst.inst θ)

theorem EnvInterp.inst_interp {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (θ : TySubst) (n : Name) (α : Ty) :
    (I.inst θ).interp n α = I.interp n (α.inst θ) := rfl

theorem EnvInterp.inst_comp {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (σ θ : TySubst) (n : Name) (α : Ty) :
    ((I.inst σ).inst θ).interp n α = (I.inst (θ.comp σ)).interp n α := by
  simp [EnvInterp.inst_interp, Ty.inst_comp]

theorem EnvInterp.inst_nil {env : Env} {ρ : TyVal}
    (I : EnvInterp env ρ) (n : Name) (α : Ty) :
    (I.inst []).interp n α = I.interp n α := by
  simp [EnvInterp.inst_interp, Ty.inst_nil]

/-- Reindex a free-variable assignment along a pointwise equality of
type universes.  Used when `ρ.inst` compositions are only propositionally
equal. -/
def FVarVal.congr {ρ ρ' : TyVal} (ξ : FVarVal ρ)
    (h : ∀ α : Ty, Ty.denote ρ α = Ty.denote ρ' α) : FVarVal ρ' where
  val := ξ.val
  mem x α := h α ▸ ξ.mem x α

@[simp] theorem FVarVal.congr_val {ρ ρ' : TyVal} (ξ : FVarVal ρ)
    (h : ∀ α : Ty, Ty.denote ρ α = Ty.denote ρ' α) (x : Name) (α : Ty) :
    (ξ.congr h).val x α = ξ.val x α := rfl

/-- Reindex an environment interpretation along the same universe equality. -/
def EnvInterp.reindex {env : Env} {ρ ρ' : TyVal} (I : EnvInterp env ρ)
    (h : ∀ α : Ty, Ty.denote ρ α = Ty.denote ρ' α) : EnvInterp env ρ' where
  interp := I.interp
  mem := fun {_n inst _gen} hconst hinst => h inst ▸ I.mem hconst hinst

@[simp] theorem EnvInterp.reindex_interp {env : Env} {ρ ρ' : TyVal}
    (I : EnvInterp env ρ) (h : ∀ α : Ty, Ty.denote ρ α = Ty.denote ρ' α)
    (n : Name) (α : Ty) :
    (I.reindex h).interp n α = I.interp n α := rfl

end HOLean
