/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Simple types

Church-style simple types with schematic (ML-style) type variables.

This is the type language of the HOL Light kernel: type variables together with
the primitive constructors `bool`, `ind`, and `fun` (`↝`).  Polymorphism is
*schematic* rather than System F — type variables are implicitly universally
quantified at the level of theorems and instantiated by `INST_TYPE`.
-/

namespace HOLean

/-- Names of schematic type variables and of free term variables. -/
abbrev Name := String

/-- Simple types of HOL. -/
inductive Ty where
  /-- A schematic type variable, e.g. `α`. -/
  | var : Name → Ty
  /-- The type of propositions / booleans. -/
  | bool : Ty
  /-- An infinite type of individuals (used by the infinity axiom). -/
  | ind : Ty
  /-- Function type `α ↝ β`. -/
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr, Inhabited

@[inherit_doc Ty.arrow]
-- Bind tighter than `=` (50) so `t = α ↝ β` means `t = (α ↝ β)`.
scoped infixr:51 " ↝ " => Ty.arrow

/-- A type substitution: the first matching pair wins. Non-variable leftovers
are ignored, matching HOL Light's `type_subst`. -/
abbrev TySubst := List (Name × Ty)

namespace TySubst

def lookup (θ : TySubst) (x : Name) : Option Ty :=
  match θ with
  | [] => none
  | (y, α) :: rest => if y = x then some α else lookup rest x

@[simp] theorem lookup_nil (x : Name) : lookup [] x = none := rfl

@[simp] theorem lookup_cons_self (x : Name) (α : Ty) (rest : TySubst) :
    lookup ((x, α) :: rest) x = some α := by
  simp [lookup]

theorem lookup_cons_of_ne {x y : Name} (α : Ty) (rest : TySubst) (h : y ≠ x) :
    lookup ((y, α) :: rest) x = lookup rest x := by
  simp [lookup, h]

end TySubst

namespace Ty

/-- Instantiate schematic type variables. -/
def inst (θ : TySubst) : Ty → Ty
  | var x => (θ.lookup x).getD (var x)
  | bool => bool
  | ind => ind
  | arrow α β => arrow (α.inst θ) (β.inst θ)

@[simp] theorem inst_bool (θ : TySubst) : bool.inst θ = bool := rfl
@[simp] theorem inst_ind (θ : TySubst) : ind.inst θ = ind := rfl
@[simp] theorem inst_var (θ : TySubst) (x : Name) :
    (var x).inst θ = (θ.lookup x).getD (var x) := rfl
@[simp] theorem inst_arrow (θ : TySubst) (α β : Ty) :
    (α ↝ β).inst θ = (α.inst θ ↝ β.inst θ) := rfl

@[simp] theorem inst_nil : ∀ α : Ty, inst [] α = α
  | var _ => rfl
  | bool => rfl
  | ind => rfl
  | arrow α β => by simp [inst, inst_nil α, inst_nil β]

/-- Free schematic type variables, left-to-right, without duplicates. -/
def tyvars : Ty → List Name
  | var x => [x]
  | bool => []
  | ind => []
  | arrow α β => α.tyvars ++ β.tyvars.filter (· ∉ α.tyvars)

theorem mem_tyvars_arrow {x : Name} {α β : Ty} :
    x ∈ (α ↝ β).tyvars ↔ x ∈ α.tyvars ∨ x ∈ β.tyvars := by
  simp [tyvars, List.mem_append, List.mem_filter]
  constructor
  · intro h
    match h with
    | Or.inl h => exact Or.inl h
    | Or.inr h => exact Or.inr h.1
  · intro h
    match h with
    | Or.inl h => exact Or.inl h
    | Or.inr h =>
      by_cases hx : x ∈ α.tyvars
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩

/-- Substitutions that agree on the free type variables of `α` instantiate it
the same way. -/
theorem inst_eq_of {α : Ty} {θ σ : TySubst}
    (h : ∀ x ∈ α.tyvars, (θ.lookup x).getD (var x) = (σ.lookup x).getD (var x)) :
    α.inst θ = α.inst σ := by
  induction α with
  | var x =>
    exact h x (by simp [tyvars])
  | bool =>
    rfl
  | ind =>
    rfl
  | arrow α β ihα ihβ =>
    rw [inst_arrow, inst_arrow, ihα, ihβ]
    · intro x hx
      exact h x (mem_tyvars_arrow.2 (Or.inr hx))
    · intro x hx
      exact h x (mem_tyvars_arrow.2 (Or.inl hx))

end Ty

namespace TySubst

/-- Compose substitutions: apply `σ`, then `θ`. First-listed bindings win. -/
def comp (σ θ : TySubst) : TySubst :=
  σ.map (fun p => (p.1, p.2.inst θ)) ++ θ

theorem lookup_append (σ θ : TySubst) (x : Name) :
    lookup (σ ++ θ) x =
      match lookup σ x with
      | some α => some α
      | none => lookup θ x := by
  induction σ with
  | nil => simp [lookup]
  | cons p σ ih =>
    obtain ⟨y, α⟩ := p
    by_cases h : y = x
    · simp [lookup, h]
    · simpa [lookup, h] using ih

theorem lookup_map_inst (σ θ : TySubst) (x : Name) :
    lookup (σ.map (fun p => (p.1, p.2.inst θ))) x =
      match lookup σ x with
      | some α => some (α.inst θ)
      | none => none := by
  induction σ with
  | nil => simp [lookup]
  | cons p σ ih =>
    obtain ⟨y, α⟩ := p
    by_cases h : y = x
    · simp [lookup, h]
    · simpa [lookup, h] using ih

theorem lookup_comp (σ θ : TySubst) (x : Name) :
    lookup (σ.comp θ) x =
      match lookup σ x with
      | some α => some (α.inst θ)
      | none => lookup θ x := by
  rw [comp, lookup_append, lookup_map_inst]
  cases lookup σ x <;> rfl

end TySubst

namespace Ty

theorem inst_comp (ty : Ty) (σ θ : TySubst) :
    (ty.inst σ).inst θ = ty.inst (σ.comp θ) := by
  induction ty with
  | var x =>
    simp [TySubst.lookup_comp]
    cases σ.lookup x <;> simp
  | bool => simp
  | ind => simp
  | arrow α β ihα ihβ => simp [ihα, ihβ]

/-- `gen` is a schematic type of which `inst` is an instance. -/
def isInstanceOf (gen inst : Ty) : Prop :=
  ∃ θ : TySubst, gen.inst θ = inst

theorem isInstanceOf_self (ty : Ty) : ty.isInstanceOf ty :=
  ⟨[], inst_nil ty⟩

theorem isInstanceOf.inst {gen inst : Ty} (h : gen.isInstanceOf inst) (θ : TySubst) :
    gen.isInstanceOf (inst.inst θ) :=
  match h with
  | ⟨σ, hσ⟩ => ⟨σ.comp θ, by rw [← inst_comp, hσ]⟩

/-- Match a generic type against an instance, accumulating bindings.
Succeeds iff the instance is a substitution instance of the pattern. -/
def matchTy : Ty → Ty → TySubst → Option TySubst
  | var x, ty, acc =>
    match acc.lookup x with
    | some ty' => if ty = ty' then some acc else none
    | none => some ((x, ty) :: acc)
  | bool, bool, acc => some acc
  | bool, _, _ => none
  | ind, ind, acc => some acc
  | ind, _, _ => none
  | arrow a b, arrow a' b', acc =>
    match a.matchTy a' acc with
    | none => none
    | some acc => b.matchTy b' acc
  | arrow _ _, _, _ => none

/-- `acc'` agrees with `acc` on every name already bound in `acc`. -/
def extendsSubst (acc acc' : TySubst) : Prop :=
  ∀ x α, acc.lookup x = some α → acc'.lookup x = some α

theorem inst_of_extends {α : Ty} {acc acc' : TySubst}
    (hext : extendsSubst acc acc')
    (hbound : ∀ x ∈ α.tyvars, (acc.lookup x).isSome = true) :
    α.inst acc' = α.inst acc := by
  induction α with
  | var x =>
    have hx : (acc.lookup x).isSome = true := hbound x (by simp [tyvars])
    cases hacc : acc.lookup x with
    | none =>
      simp [hacc] at hx
    | some α =>
      have := hext x α hacc
      simp [inst, hacc, this]
  | bool => simp
  | ind => simp
  | arrow α β ihα ihβ =>
    change (α.inst acc' ↝ β.inst acc') = (α.inst acc ↝ β.inst acc)
    rw [ihα (fun x hx => hbound x (mem_tyvars_arrow.2 (Or.inl hx)))]
    rw [ihβ (fun x hx => hbound x (mem_tyvars_arrow.2 (Or.inr hx)))]

theorem matchTy_spec {pat ty : Ty} {acc acc' : TySubst}
    (h : pat.matchTy ty acc = some acc') :
    extendsSubst acc acc' ∧
      (∀ x ∈ pat.tyvars, (acc'.lookup x).isSome = true) ∧
      pat.inst acc' = ty := by
  induction pat generalizing ty acc acc' with
  | var x =>
    cases hacc : acc.lookup x with
    | some ty' =>
      simp [matchTy, hacc] at h
      by_cases hty : ty = ty'
      · simp [hty] at h
        cases h
        refine ⟨fun y β hy => hy, ?_, ?_⟩
        · intro y hy
          simp [tyvars] at hy
          subst hy
          simp [hacc]
        · simp [inst, hacc, hty]
      · simp [hty] at h
    | none =>
      simp [matchTy, hacc] at h
      cases h
      refine ⟨?_, ?_, ?_⟩
      · intro y β hy
        by_cases hx : x = y
        · subst hx
          simp [hacc] at hy
        · simpa [TySubst.lookup, hx] using hy
      · intro y hy
        simp [tyvars] at hy
        subst hy
        simp [TySubst.lookup]
      · simp [inst, TySubst.lookup]
  | bool =>
    cases ty with
    | bool =>
      simp [matchTy] at h
      cases h
      exact ⟨fun _ _ hy => hy, by simp [tyvars], rfl⟩
    | var _ => simp [matchTy] at h
    | ind => simp [matchTy] at h
    | arrow _ _ => simp [matchTy] at h
  | ind =>
    cases ty with
    | ind =>
      simp [matchTy] at h
      cases h
      exact ⟨fun _ _ hy => hy, by simp [tyvars], rfl⟩
    | var _ => simp [matchTy] at h
    | bool => simp [matchTy] at h
    | arrow _ _ => simp [matchTy] at h
  | arrow α β ihα ihβ =>
    cases ty with
    | arrow α' β' =>
      simp [matchTy] at h
      cases hα : α.matchTy α' acc with
      | none =>
        simp [hα] at h
      | some acc1 =>
        simp [hα] at h
        obtain ⟨hext1, hbound1, hαinst⟩ := ihα hα
        obtain ⟨hext2, hbound2, hβinst⟩ := ihβ h
        refine ⟨?_, ?_, ?_⟩
        · intro x γ hx
          exact hext2 x γ (hext1 x γ hx)
        · intro x hx
          match mem_tyvars_arrow.1 hx with
          | Or.inl hxα =>
            cases hlook : acc1.lookup x with
            | none =>
              have := hbound1 x hxα
              simp [hlook] at this
            | some γ =>
              have := hext2 x γ hlook
              simp [this]
          | Or.inr hxβ =>
            exact hbound2 x hxβ
        · have hα' : α.inst acc' = α.inst acc1 :=
            inst_of_extends hext2 (fun x hx => hbound1 x hx)
          simp [inst, hα', hαinst, hβinst]
    | var _ => simp [matchTy] at h
    | bool => simp [matchTy] at h
    | ind => simp [matchTy] at h

theorem matchTy_sound {pat ty : Ty} {acc acc' : TySubst}
    (h : pat.matchTy ty acc = some acc') :
    pat.inst acc' = ty :=
  (matchTy_spec h).2.2

/-- Partial substitution `acc` agrees with `θ` on every name it binds. -/
def agrees (acc θ : TySubst) : Prop :=
  ∀ x α, acc.lookup x = some α → α = (θ.lookup x).getD (var x)

theorem agrees_nil (θ : TySubst) : agrees [] θ := by
  intro x α h
  simp [TySubst.lookup] at h

theorem matchTy_complete {pat : Ty} {θ acc : TySubst} (h : agrees acc θ) :
    ∃ acc', pat.matchTy (pat.inst θ) acc = some acc' ∧ agrees acc' θ := by
  induction pat generalizing acc with
  | var x =>
    cases hacc : acc.lookup x with
    | some α =>
      have heq : α = (θ.lookup x).getD (var x) := h x α hacc
      refine ⟨acc, ?_, h⟩
      simp [matchTy, inst, hacc, heq]
    | none =>
      refine ⟨(x, (θ.lookup x).getD (var x)) :: acc, ?_, ?_⟩
      · simp [matchTy, inst, hacc]
      · intro y β hy
        by_cases hx : x = y
        · subst hx
          simp [TySubst.lookup] at hy
          cases hy
          rfl
        · simp [TySubst.lookup, hx] at hy
          exact h y β hy
  | bool =>
    exact ⟨acc, by simp [matchTy], h⟩
  | ind =>
    exact ⟨acc, by simp [matchTy], h⟩
  | arrow α β ihα ihβ =>
    obtain ⟨acc1, h1, ha1⟩ := ihα h
    obtain ⟨acc2, h2, ha2⟩ := ihβ ha1
    refine ⟨acc2, ?_, ha2⟩
    simp [matchTy, inst, h1, h2]

theorem isInstanceOf_of_matchTy {gen inst : Ty} {acc acc' : TySubst}
    (h : gen.matchTy inst acc = some acc') :
    gen.isInstanceOf inst :=
  ⟨acc', matchTy_sound h⟩

theorem matchTy_of_isInstanceOf {gen inst : Ty} (h : gen.isInstanceOf inst) :
    (gen.matchTy inst []).isSome = true := by
  obtain ⟨θ, hθ⟩ := h
  obtain ⟨acc', hm, _⟩ := matchTy_complete (pat := gen) (θ := θ) (acc := []) (agrees_nil θ)
  rw [hθ] at hm
  simp [hm]

theorem isInstanceOf_of_isSome {gen inst : Ty}
    (h : (gen.matchTy inst []).isSome = true) :
    gen.isInstanceOf inst := by
  cases hm : gen.matchTy inst [] with
  | none => simp [hm] at h
  | some acc => exact isInstanceOf_of_matchTy hm

end Ty

/-!
Bound-variable contexts are ordinary lists.  Index `0` is the innermost
binder, so lookup is `Γ[i]?` (`List.getElem?`) and inserting a binder at
depth `c` is `Γ.insertIdx c γ`.
-/

/-- Lookup in a snoc-context: the last index is the extra binder. -/
theorem List.getElem?_snoc (Δ : List Ty) (α : Ty) (i : Nat) :
    (Δ ++ [α])[i]? = if i = Δ.length then some α else Δ[i]? := by
  induction Δ generalizing i with
  | nil =>
    cases i <;> simp
  | cons γ Δ ih =>
    cases i with
    | zero =>
      simp
    | succ n =>
      simpa using ih n

end HOLean
