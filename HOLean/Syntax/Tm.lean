/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Const

/-!
# Terms

Locally nameless terms for HOL Light's four constructors:

* bound variables (`bvar`) — de Bruijn indices
* free variables (`fvar`) — HOL-style pairs `(name, type)`
* constants (`const`) — a name plus its *instantiated* type
* application and λ-abstraction

The type stored on `const n inst` is the type of that occurrence, not a
type argument.  It must be an instance of the constant's generic type in
the environment (`Ty.instantiates`).

Locally nameless syntax avoids HOL Light's `Clash` during `INST_TYPE`: a type
instantiation cannot capture a free variable by a binder, because binders are
indices.
-/

namespace HOLean

/-- Raw HOL terms.  Well-typedness is a separate judgment (`HasType`). -/
inductive Tm where
  /-- Bound variable, de Bruijn index (`0` = innermost binder). -/
  | bvar : Nat → Tm
  /-- Free variable, identified by *both* name and type (HOL Light). -/
  | fvar : Name → Ty → Tm
  /-- Constant `n` at instantiated type `inst`. -/
  | const : Name → Ty → Tm
  /-- Application. -/
  | app : Tm → Tm → Tm
  /-- λ-abstraction; the binder type is stored, the bound name is not. -/
  | lam : Ty → Tm → Tm
  deriving DecidableEq, Repr, Inhabited

namespace Tm

/-- Replace bound index `k` by the (locally closed) term `u`. -/
def openAt (t : Tm) (k : Nat) (u : Tm) : Tm :=
  match t with
  | bvar i => if i = k then u else bvar i
  | fvar x α => fvar x α
  | const c α => const c α
  | app f a => app (f.openAt k u) (a.openAt k u)
  | lam α t => lam α (t.openAt (k + 1) u)

@[simp] def open' (t u : Tm) : Tm := t.openAt 0 u

/-- Replace the free variable `(x, α)` at depth `k` by a bound index. -/
def closeAt (t : Tm) (k : Nat) (x : Name) (α : Ty) : Tm :=
  match t with
  | bvar i => bvar i
  | fvar y β => if y = x ∧ β = α then bvar k else fvar y β
  | const c β => const c β
  | app f a => app (f.closeAt k x α) (a.closeAt k x α)
  | lam β t => lam β (t.closeAt (k + 1) x α)

@[simp] def close (t : Tm) (x : Name) (α : Ty) : Tm := t.closeAt 0 x α

/-- HOL Light `mk_abs`: abstract the free variable `(x, α)`. -/
def abstract (t : Tm) (x : Name) (α : Ty) : Tm :=
  lam α (t.close x α)

/-- Does `t` mention the constant `n`? -/
def hasConst : Tm → Name → Bool
  | const c _, n => decide (c = n)
  | app f a, n => f.hasConst n || a.hasConst n
  | lam _ t, n => t.hasConst n
  | _, _ => false

/-- Is the HOL variable `(x, α)` free in `t`?  Binders do not shadow free
variables (locally nameless). -/
def freeIn (t : Tm) (x : Name) (α : Ty) : Bool :=
  match t with
  | bvar _ => false
  | fvar y β => decide (y = x ∧ β = α)
  | const _ _ => false
  | app f a => f.freeIn x α || a.freeIn x α
  | lam _ t => t.freeIn x α

/-- Type instantiation of every type annotation in a term. -/
def instTy (t : Tm) (θ : TySubst) : Tm :=
  match t with
  | bvar i => bvar i
  | fvar x α => fvar x (α.inst θ)
  | const c α => const c (α.inst θ)
  | app f a => app (f.instTy θ) (a.instTy θ)
  | lam α t => lam (α.inst θ) (t.instTy θ)

@[simp] theorem instTy_bvar (θ : TySubst) (i : Nat) : (bvar i).instTy θ = bvar i := rfl
@[simp] theorem instTy_fvar (θ : TySubst) (x : Name) (α : Ty) :
    (fvar x α).instTy θ = fvar x (α.inst θ) := rfl
@[simp] theorem instTy_const (θ : TySubst) (n : Name) (α : Ty) :
    (const n α).instTy θ = const n (α.inst θ) := rfl
@[simp] theorem instTy_app (θ : TySubst) (f a : Tm) :
    (app f a).instTy θ = app (f.instTy θ) (a.instTy θ) := rfl
@[simp] theorem instTy_lam (θ : TySubst) (α : Ty) (t : Tm) :
    (lam α t).instTy θ = lam (α.inst θ) (t.instTy θ) := rfl

@[simp] theorem instTy_nil : ∀ t : Tm, t.instTy [] = t
  | bvar _ => rfl
  | fvar _ _ => by simp [instTy]
  | const _ _ => by simp [instTy]
  | app f a => by simp [instTy, instTy_nil f, instTy_nil a]
  | lam α t => by simp [instTy, instTy_nil t]

/-- Substitute a single free variable.  Capture-free when `u` is locally closed. -/
def substFvar (t : Tm) (x : Name) (α : Ty) (u : Tm) : Tm :=
  match t with
  | bvar i => bvar i
  | fvar y β => if y = x ∧ β = α then u else fvar y β
  | const c β => const c β
  | app f a => app (f.substFvar x α u) (a.substFvar x α u)
  | lam β t => lam β (t.substFvar x α u)

@[simp] theorem substFvar_bvar (x : Name) (α : Ty) (u : Tm) (i : Nat) :
    (bvar i).substFvar x α u = bvar i := rfl

@[simp] theorem substFvar_const (x : Name) (α : Ty) (u : Tm) (n : Name) (β : Ty) :
    (const n β).substFvar x α u = const n β := rfl

theorem substFvar_fvar_self (x : Name) (α : Ty) (u : Tm) :
    (fvar x α).substFvar x α u = u := by
  simp [substFvar]

theorem substFvar_fvar_of_ne (x : Name) (α : Ty) (u : Tm) (y : Name) (β : Ty)
    (h : ¬ (y = x ∧ β = α)) :
    (fvar y β).substFvar x α u = fvar y β := by
  simp [substFvar, h]

/-- Simultaneous term substitution, HOL Light `vsubst`. -/
abbrev Subst := List (Name × Ty × Tm)

def Subst.lookup (σ : Subst) (x : Name) (α : Ty) : Option Tm :=
  match σ with
  | [] => none
  | (y, β, u) :: rest => if y = x ∧ β = α then some u else lookup rest x α

def applySubst (t : Tm) (σ : Subst) : Tm :=
  match t with
  | bvar i => bvar i
  | fvar x α =>
    match σ.lookup x α with
    | some u => u
    | none => fvar x α
  | const c α => const c α
  | app f a => app (f.applySubst σ) (a.applySubst σ)
  | lam α t => lam α (t.applySubst σ)

/-- Equality constant at type `α ↝ α ↝ bool`. -/
def eqConst (α : Ty) : Tm :=
  const eqName (α ↝ α ↝ .bool)

/-- Hilbert-choice constant at type `(α ↝ bool) ↝ α`. -/
def selectConst (α : Ty) : Tm :=
  const selectName ((α ↝ .bool) ↝ α)

/-- `s = t` at type `α`, i.e. `(=) : α ↝ α ↝ bool` applied to `s` and `t`. -/
def mkEq (α : Ty) (s t : Tm) : Tm :=
  app (app (eqConst α) s) t

@[simp] theorem mkEq_eq (α : Ty) (s t : Tm) :
    mkEq α s t = app (app (eqConst α) s) t := rfl

@[simp] theorem eqConst_eq (α : Ty) :
    eqConst α = const eqName (α ↝ α ↝ .bool) := rfl

/-- Destructor for equations. -/
def destEq : Tm → Option (Ty × Tm × Tm)
  | app (app (const n (.arrow α (.arrow β .bool))) s) t =>
      if n = eqName ∧ α = β then some (α, s, t) else none
  | _ => none

@[simp] theorem destEq_mkEq (α : Ty) (s t : Tm) :
    destEq (mkEq α s t) = some (α, s, t) := by
  simp [destEq, mkEq, eqConst]

/-- Inverse of `destEq_mkEq`: a successful destructor recovers `mkEq`. -/
theorem destEq_eq {e α s t} (h : destEq e = some (α, s, t)) : e = mkEq α s t := by
  cases e with
  | app f a =>
    cases f with
    | app g b =>
      cases g with
      | const n τ =>
        cases τ with
        | arrow α' rest =>
          cases rest with
          | arrow β γ =>
            cases γ with
            | bool =>
              dsimp [destEq] at h
              by_cases hcond : n = eqName ∧ α' = β
              · simp [hcond] at h
                obtain ⟨rfl, rfl⟩ := hcond
                obtain ⟨rfl, rfl, rfl⟩ := h
                simp [mkEq, eqConst]
              · simp [hcond] at h
            | var _ => simp [destEq] at h
            | ind => simp [destEq] at h
            | arrow _ _ => simp [destEq] at h
          | var _ => simp [destEq] at h
          | bool => simp [destEq] at h
          | ind => simp [destEq] at h
        | var _ => simp [destEq] at h
        | bool => simp [destEq] at h
        | ind => simp [destEq] at h
      | bvar _ => simp [destEq] at h
      | fvar _ _ => simp [destEq] at h
      | app _ _ => simp [destEq] at h
      | lam _ _ => simp [destEq] at h
    | bvar _ => simp [destEq] at h
    | fvar _ _ => simp [destEq] at h
    | const _ _ => simp [destEq] at h
    | lam _ _ => simp [destEq] at h
  | bvar _ => simp [destEq] at h
  | fvar _ _ => simp [destEq] at h
  | const _ _ => simp [destEq] at h
  | lam _ _ => simp [destEq] at h

/-- Schematic type variables occurring in a term. -/
def tyvars : Tm → List Name
  | bvar _ => []
  | fvar _ α => α.tyvars
  | const _ α => α.tyvars
  | app f a => f.tyvars ++ a.tyvars.filter (· ∉ f.tyvars)
  | lam α t => α.tyvars ++ t.tyvars.filter (· ∉ α.tyvars)

theorem mem_tyvars_app {x : Name} {f a : Tm} :
    x ∈ (app f a).tyvars ↔ x ∈ f.tyvars ∨ x ∈ a.tyvars := by
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
      by_cases hx : x ∈ f.tyvars
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩

theorem mem_tyvars_lam {x : Name} {α : Ty} {t : Tm} :
    x ∈ (lam α t).tyvars ↔ x ∈ α.tyvars ∨ x ∈ t.tyvars := by
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

/-- Substitutions that agree on the type variables of `t` instantiate it
the same way. -/
theorem instTy_eq_of (t : Tm) {θ σ : TySubst}
    (h : ∀ x ∈ t.tyvars, (θ.lookup x).getD (Ty.var x) = (σ.lookup x).getD (Ty.var x)) :
    t.instTy θ = t.instTy σ := by
  induction t with
  | bvar i =>
    rfl
  | fvar y α =>
    simp [instTy, Ty.inst_eq_of (α := α) h]
  | const n α =>
    simp [instTy, Ty.inst_eq_of (α := α) h]
  | app f a ihf iha =>
    simp [instTy, ihf (fun x hx => h x (mem_tyvars_app.2 (Or.inl hx))),
      iha (fun x hx => h x (mem_tyvars_app.2 (Or.inr hx)))]
  | lam α t ih =>
    simp [instTy, Ty.inst_eq_of (α := α) (fun x hx => h x (mem_tyvars_lam.2 (Or.inl hx))),
      ih (fun x hx => h x (mem_tyvars_lam.2 (Or.inr hx)))]

/-- Matching `ty` against `ty.inst θ` recovers `rhs[θ]`, provided every
schematic variable of `rhs` already occurs in `ty`. -/
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

/-- Increment every bound index `≥ c` by `d`.  Used when a term is placed
under additional λ-binders (so connectives do not capture). -/
def shift (t : Tm) (d c : Nat) : Tm :=
  match t with
  | bvar i => if i < c then bvar i else bvar (i + d)
  | fvar x α => fvar x α
  | const k α => const k α
  | app f a => app (f.shift d c) (a.shift d c)
  | lam α t => lam α (t.shift d (c + 1))

/-- Locally closed at cutoff `n`: every bound index is `< n`.
`LC t 0` means `t` has no dangling `bvar`s.  α-equivalent named terms
are *identical* once written this way — binders carry no names. -/
def LC (t : Tm) (n : Nat) : Bool :=
  match t with
  | bvar i => decide (i < n)
  | fvar _ _ => true
  | const _ _ => true
  | app f a => f.LC n && a.LC n
  | lam _ t => t.LC (n + 1)

@[simp] theorem LC_bvar (i n : Nat) : (bvar i).LC n = decide (i < n) := rfl
@[simp] theorem LC_fvar (x : Name) (α : Ty) (n : Nat) : (fvar x α).LC n = true := rfl
@[simp] theorem LC_const (n : Name) (α : Ty) (k : Nat) : (const n α).LC k = true := rfl
@[simp] theorem LC_app (f a : Tm) (n : Nat) : (app f a).LC n = (f.LC n && a.LC n) := rfl
@[simp] theorem LC_lam (α : Ty) (t : Tm) (n : Nat) : (lam α t).LC n = t.LC (n + 1) := rfl

theorem freeIn_bvar (i : Nat) (x : Name) (α : Ty) : (bvar i).freeIn x α = false := rfl

theorem closeAt_fresh {t : Tm} {x : Name} {α : Ty} {k : Nat}
    (h : t.freeIn x α = false) : t.closeAt k x α = t := by
  induction t generalizing k with
  | bvar i =>
    simp [closeAt]
  | fvar y β =>
    simp [freeIn] at h
    by_cases hy : y = x ∧ β = α
    · exact (h hy.1 hy.2).elim
    · simp [closeAt, hy]
  | const c β =>
    simp [closeAt]
  | app f a ihf iha =>
    simp [freeIn] at h
    simp [closeAt, ihf h.1, iha h.2]
  | lam β t ih =>
    simp [freeIn] at h
    simp [closeAt, ih h]

theorem LC_le {t : Tm} {n m : Nat} (hn : t.LC n = true) (hle : n ≤ m) :
    t.LC m = true := by
  induction t generalizing n m with
  | bvar i =>
    simp [LC] at hn ⊢
    exact Nat.lt_of_lt_of_le hn hle
  | fvar _ _ => simp [LC]
  | const _ _ => simp [LC]
  | app f a ihf iha =>
    simp [LC] at hn ⊢
    exact ⟨ihf hn.1 hle, iha hn.2 hle⟩
  | lam α t ih =>
    simp [LC] at hn ⊢
    exact ih hn (Nat.succ_le_succ hle)

theorem shift_of_LC {t : Tm} {d c : Nat} (h : t.LC c = true) : t.shift d c = t := by
  induction t generalizing c with
  | bvar i =>
    simp [LC] at h
    simp [shift, Nat.not_le_of_gt h]
  | fvar x α =>
    simp [shift]
  | const k α =>
    simp [shift]
  | app f a ihf iha =>
    simp [LC] at h
    simp [shift, ihf h.1, iha h.2]
  | lam α t ih =>
    simp [LC] at h
    simp [shift, ih h]

theorem shift_of_LC0 {t : Tm} {d c : Nat} (h : t.LC 0 = true) : t.shift d c = t :=
  shift_of_LC (LC_le h (Nat.zero_le c))

theorem openAt_of_LC {t u : Tm} {k : Nat} (h : t.LC k = true) : t.openAt k u = t := by
  induction t generalizing k with
  | bvar i =>
    simp [LC] at h
    simp [openAt, Nat.ne_of_lt h]
  | fvar x α =>
    simp [openAt]
  | const k' α =>
    simp [openAt]
  | app f a ihf iha =>
    simp [LC] at h
    simp [openAt, ihf h.1, iha h.2]
  | lam α t ih =>
    simp [LC] at h
    simp [openAt, ih h]

/-- Closing a free variable and immediately opening it is the identity on
terms that do not mention bound index `k`. -/
theorem openAt_closeAt {t : Tm} {x : Name} {α : Ty} {k : Nat}
    (h : t.LC k = true) :
    (t.closeAt k x α).openAt k (.fvar x α) = t := by
  induction t generalizing k with
  | bvar i =>
    simp [LC] at h
    simp [closeAt, openAt, Nat.ne_of_lt h]
  | fvar y β =>
    by_cases hy : y = x ∧ β = α
    · simp [closeAt, openAt, hy]
    · simp [closeAt, openAt, hy]
  | const c β =>
    simp [closeAt, openAt]
  | app f a ihf iha =>
    simp [LC] at h
    simp [closeAt, openAt, ihf h.1, iha h.2]
  | lam β t ih =>
    simp [LC] at h
    simp [closeAt, openAt, ih h]

/-- Opening a dangling index as a *fresh* free variable, then closing it,
restores the original term. -/
theorem closeAt_openAt {t : Tm} {x : Name} {α : Ty} {k : Nat}
    (hLC : t.LC (k + 1) = true) (hf : t.freeIn x α = false) :
    (t.openAt k (.fvar x α)).closeAt k x α = t := by
  induction t generalizing k with
  | bvar i =>
    simp [LC] at hLC
    by_cases hi : i = k
    · simp [openAt, closeAt, hi]
    · simp [openAt, closeAt, hi]
  | fvar y β =>
    simp [freeIn] at hf
    by_cases hy : y = x ∧ β = α
    · exact (hf hy.1 hy.2).elim
    · simp [openAt, closeAt, hy]
  | const c β =>
    simp [openAt, closeAt]
  | app f a ihf iha =>
    simp [LC, freeIn] at hLC hf
    simp [openAt, closeAt, ihf hLC.1 hf.1, iha hLC.2 hf.2]
  | lam β t ih =>
    simp [LC, freeIn] at hLC hf
    simp [openAt, closeAt, ih hLC hf]

@[simp] theorem open_close {t : Tm} {x : Name} {α : Ty} (h : t.LC 0 = true) :
    (t.close x α).open' (.fvar x α) = t :=
  openAt_closeAt h

@[simp] theorem close_open {t : Tm} {x : Name} {α : Ty}
    (hLC : t.LC 1 = true) (hf : t.freeIn x α = false) :
    (t.open' (.fvar x α)).close x α = t :=
  closeAt_openAt hLC hf

theorem instTy_comp (t : Tm) (σ θ : TySubst) :
    (t.instTy σ).instTy θ = t.instTy (σ.comp θ) := by
  induction t with
  | bvar i => rfl
  | fvar x α => simp [instTy, Ty.inst_comp]
  | const n α => simp [instTy, Ty.inst_comp]
  | app f a ihf iha => simp [instTy, ihf, iha]
  | lam α t ih => simp [instTy, Ty.inst_comp, ih]

/-- Replace occurrences of defined constant `n` by the matching instance of `rhs`.
If `inst` is not an instance of the generic type `ty`, the constant is left alone. -/
def unfoldDef (t : Tm) (n : Name) (ty : Ty) (rhs : Tm) : Tm :=
  match t with
  | const c inst =>
      if c = n then
        match ty.matchTy inst [] with
        | some σ => rhs.instTy σ
        | none => const c inst
      else const c inst
  | app f a => app (f.unfoldDef n ty rhs) (a.unfoldDef n ty rhs)
  | lam α t => lam α (t.unfoldDef n ty rhs)
  | t => t

theorem unfoldDef_bvar (n : Name) (ty : Ty) (rhs : Tm) (i : Nat) :
    (bvar i).unfoldDef n ty rhs = bvar i := rfl

theorem unfoldDef_fvar (n : Name) (ty : Ty) (rhs : Tm) (x : Name) (α : Ty) :
    (fvar x α).unfoldDef n ty rhs = fvar x α := rfl

theorem unfoldDef_app (n : Name) (ty : Ty) (rhs : Tm) (f a : Tm) :
    (app f a).unfoldDef n ty rhs =
      app (f.unfoldDef n ty rhs) (a.unfoldDef n ty rhs) := rfl

theorem unfoldDef_lam (n : Name) (ty : Ty) (rhs : Tm) (α : Ty) (t : Tm) :
    (lam α t).unfoldDef n ty rhs = lam α (t.unfoldDef n ty rhs) := rfl

theorem unfoldDef_const_of_ne (n : Name) (ty : Ty) (rhs : Tm) {c : Name} (α : Ty)
    (hne : c ≠ n) :
    (const c α).unfoldDef n ty rhs = const c α := by
  simp [unfoldDef, hne]

theorem unfoldDef_const_self (n : Name) (ty : Ty) (rhs : Tm) (inst : Ty) :
    (const n inst).unfoldDef n ty rhs =
      match ty.matchTy inst [] with
      | some σ => rhs.instTy σ
      | none => const n inst := by
  simp [unfoldDef]

theorem unfoldDef_of_not_hasConst (n : Name) (ty : Ty) (rhs : Tm) (t : Tm)
    (h : t.hasConst n = false) :
    t.unfoldDef n ty rhs = t := by
  induction t with
  | bvar i => rfl
  | fvar x α => rfl
  | const c α =>
    simp [hasConst] at h
    exact unfoldDef_const_of_ne n ty rhs α h
  | app f a ihf iha =>
    simp [hasConst, Bool.or_eq_false_iff] at h
    simp [unfoldDef, ihf h.1, iha h.2]
  | lam α t ih =>
    simp [hasConst] at h
    simp [unfoldDef, ih h]

theorem unfoldDef_mkEq (n : Name) (ty : Ty) (rhs : Tm) (α : Ty) (s t : Tm)
    (hne_eq : n ≠ eqName) :
    (mkEq α s t).unfoldDef n ty rhs =
      mkEq α (s.unfoldDef n ty rhs) (t.unfoldDef n ty rhs) := by
  have hne : eqName ≠ n := Ne.symm hne_eq
  simp [mkEq, eqConst, unfoldDef, hne]

theorem freeIn_instTy_false (t : Tm) (σ : TySubst)
    (h : ∀ x α, t.freeIn x α = false) (x : Name) (α : Ty) :
    (t.instTy σ).freeIn x α = false := by
  induction t generalizing σ with
  | bvar i => rfl
  | fvar y β =>
    have := h y β
    simp [freeIn] at this
  | const c β => rfl
  | app f a ihf iha =>
    have hf : ∀ x α, f.freeIn x α = false := fun x α => by
      have := h x α; simp [freeIn] at this; exact this.1
    have ha : ∀ x α, a.freeIn x α = false := fun x α => by
      have := h x α; simp [freeIn] at this; exact this.2
    simp [instTy, freeIn, ihf σ hf, iha σ ha]
  | lam β t ih =>
    have ht : ∀ x α, t.freeIn x α = false := fun x α => by
      simpa [freeIn] using h x α
    simp [instTy, freeIn, ih σ ht]

theorem applySubst_of_not_freeIn (t : Tm) (σ : Subst)
    (h : ∀ x α, t.freeIn x α = false) :
    t.applySubst σ = t := by
  induction t with
  | bvar i => rfl
  | fvar y β =>
    have := h y β
    simp [freeIn] at this
  | const c β => rfl
  | app f a ihf iha =>
    have hf : ∀ x α, f.freeIn x α = false := fun x α => by
      have := h x α; simp [freeIn] at this; exact this.1
    have ha : ∀ x α, a.freeIn x α = false := fun x α => by
      have := h x α; simp [freeIn] at this; exact this.2
    simp [applySubst, ihf hf, iha ha]
  | lam β t ih =>
    have ht : ∀ x α, t.freeIn x α = false := fun x α => by
      simpa [freeIn] using h x α
    simp [applySubst, ih ht]

theorem unfoldDef_freeIn (n : Name) (ty : Ty) (rhs : Tm) (t : Tm)
    (hclosed : ∀ x α, rhs.freeIn x α = false) (x : Name) (α : Ty) :
    (t.unfoldDef n ty rhs).freeIn x α = t.freeIn x α := by
  induction t with
  | bvar i => rfl
  | fvar y β => rfl
  | const c β =>
    by_cases hc : c = n
    · subst hc
      simp only [unfoldDef, ↓reduceIte]
      cases hθ : ty.matchTy β [] with
      | none => rfl
      | some σ =>
        exact (freeIn_instTy_false rhs σ hclosed x α).trans rfl
    · simp [unfoldDef, hc]
  | app f a ihf iha =>
    simp [unfoldDef, freeIn, ihf, iha]
  | lam β t ih =>
    simp [unfoldDef, freeIn, ih]

theorem Subst.lookup_map_unfoldDef (n : Name) (ty : Ty) (rhs : Tm) (σ : Subst)
    (x : Name) (α : Ty) :
    Subst.lookup (σ.map fun p => (p.1, p.2.1, p.2.2.unfoldDef n ty rhs)) x α =
      Option.map (·.unfoldDef n ty rhs) (Subst.lookup σ x α) := by
  induction σ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨y, β, u⟩ := p
    by_cases hy : y = x ∧ β = α
    · simp [Subst.lookup, List.map, hy]
    · simp [Subst.lookup, List.map, hy, ih]

theorem unfoldDef_applySubst (n : Name) (ty : Ty) (rhs : Tm) (t : Tm) (σ : Subst)
    (hclosed : ∀ x α, rhs.freeIn x α = false) :
    (t.applySubst σ).unfoldDef n ty rhs =
      (t.unfoldDef n ty rhs).applySubst
        (σ.map fun p => (p.1, p.2.1, p.2.2.unfoldDef n ty rhs)) := by
  induction t with
  | bvar i => rfl
  | fvar x α =>
    simp only [applySubst, unfoldDef_fvar, Subst.lookup_map_unfoldDef]
    cases σ.lookup x α <;> simp [unfoldDef_fvar]
  | const c α =>
    by_cases hc : c = n
    · subst hc
      simp only [applySubst, unfoldDef_const_self]
      cases ty.matchTy α [] with
      | none =>
        simp [applySubst]
      | some τ =>
        simp [applySubst_of_not_freeIn _ _ (freeIn_instTy_false rhs τ hclosed)]
    · simp [applySubst, unfoldDef_const_of_ne n ty rhs α hc]
  | app f a ihf iha =>
    simp [applySubst, unfoldDef, ihf, iha]
  | lam α t ih =>
    simp [applySubst, unfoldDef, ih]

theorem unfoldDef_closeAt (n : Name) (ty : Ty) (rhs : Tm) (t : Tm)
    (k : Nat) (x : Name) (α : Ty)
    (hclosed : ∀ y β, rhs.freeIn y β = false) :
    (t.closeAt k x α).unfoldDef n ty rhs =
      (t.unfoldDef n ty rhs).closeAt k x α := by
  induction t generalizing k with
  | bvar i => rfl
  | fvar y β =>
    by_cases hy : y = x ∧ β = α
    · simp [closeAt, hy, unfoldDef_fvar, unfoldDef_bvar]
    · simp [closeAt, hy, unfoldDef_fvar]
  | const c β =>
    by_cases hc : c = n
    · subst hc
      simp only [closeAt, unfoldDef_const_self]
      cases ty.matchTy β [] with
      | none => simp [closeAt]
      | some σ =>
        have : (rhs.instTy σ).closeAt k x α = rhs.instTy σ :=
          closeAt_fresh (freeIn_instTy_false rhs σ hclosed x α)
        simp [this]
    · simp [closeAt, unfoldDef_const_of_ne n ty rhs β hc]
  | app f a ihf iha =>
    simp [closeAt, unfoldDef, ihf, iha]
  | lam β t ih =>
    simp [closeAt, unfoldDef, ih]

theorem unfoldDef_abstract (n : Name) (ty : Ty) (rhs : Tm) (t : Tm)
    (x : Name) (α : Ty)
    (hclosed : ∀ y β, rhs.freeIn y β = false) :
    (t.abstract x α).unfoldDef n ty rhs =
      (t.unfoldDef n ty rhs).abstract x α := by
  simp [abstract, unfoldDef_lam, unfoldDef_closeAt n ty rhs t 0 x α hclosed]

theorem LC_instTy (t : Tm) (θ : TySubst) (k : Nat) :
    (t.instTy θ).LC k = t.LC k := by
  induction t generalizing k with
  | bvar i => rfl
  | fvar _ _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp [instTy, LC, ihf, iha]
  | lam α t ih => simp [instTy, LC, ih]

theorem unfoldDef_openAt (n : Name) (ty : Ty) (rhs : Tm) (t u : Tm) (k : Nat)
    (_hclosed : ∀ y β, rhs.freeIn y β = false) (hLC : rhs.LC 0 = true) :
    (t.openAt k u).unfoldDef n ty rhs =
      (t.unfoldDef n ty rhs).openAt k (u.unfoldDef n ty rhs) := by
  induction t generalizing k with
  | bvar i =>
    by_cases hi : i = k
    · simp [openAt, hi, unfoldDef_bvar]
    · simp [openAt, hi, unfoldDef_bvar]
  | fvar y β => simp [openAt, unfoldDef_fvar]
  | const c β =>
    by_cases hc : c = n
    · subst hc
      simp only [openAt, unfoldDef_const_self]
      cases ty.matchTy β [] with
      | none => simp [openAt]
      | some σ =>
        have hLCσ : (rhs.instTy σ).LC k = true :=
          LC_le (by simpa [LC_instTy] using hLC) (Nat.zero_le k)
        have : (rhs.instTy σ).openAt k (u.unfoldDef c ty rhs) = rhs.instTy σ :=
          openAt_of_LC hLCσ
        simp [this]
    · simp [openAt, unfoldDef_const_of_ne n ty rhs β hc]
  | app f a ihf iha =>
    simp [openAt, unfoldDef, ihf, iha]
  | lam β t ih =>
    simp [openAt, unfoldDef, ih]

theorem unfoldDef_open' (n : Name) (ty : Ty) (rhs : Tm) (t u : Tm)
    (hclosed : ∀ y β, rhs.freeIn y β = false) (hLC : rhs.LC 0 = true) :
    (t.open' u).unfoldDef n ty rhs =
      (t.unfoldDef n ty rhs).open' (u.unfoldDef n ty rhs) :=
  unfoldDef_openAt n ty rhs t u 0 hclosed hLC

theorem unfoldDef_const_generic (n : Name) (ty : Ty) (rhs : Tm)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars) :
    (const n ty).unfoldDef n ty rhs = rhs := by
  obtain ⟨σ, hσ, hag⟩ := Ty.matchTy_inst_agrees ty ([] : TySubst)
  have hσ' : ty.matchTy ty [] = some σ := by simpa [Ty.inst_nil] using hσ
  rw [unfoldDef_const_self, hσ']
  exact (instTy_eq_of_match hvars hσ hag).trans (instTy_nil rhs)

/-- Unfolding `const n` after type instantiation, when `inst` is already an
instance of the generic type. -/
theorem unfoldDef_const_instTy (n : Name) (ty : Ty) (rhs : Tm) (inst : Ty)
    (θ : TySubst) (hinst : ty.instantiates inst)
    (hvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars) :
    (const n (inst.inst θ)).unfoldDef n ty rhs =
      ((const n inst).unfoldDef n ty rhs).instTy θ := by
  have hsome := Ty.matchTy_of_instantiates hinst
  cases hm : ty.matchTy inst [] with
  | none => simp [hm] at hsome
  | some τ =>
    have hsound : ty.inst τ = inst := Ty.matchTy_sound hm
    obtain ⟨τ', hm', hag⟩ := Ty.matchTy_inst_agrees ty (τ.comp θ)
    have heq : ty.inst (τ.comp θ) = inst.inst θ := by
      rw [← Ty.inst_comp, hsound]
    have hm'' : ty.matchTy (inst.inst θ) [] = some τ' := by
      rwa [← heq]
    simp [unfoldDef_const_self, hm, hm'', instTy_comp]
    exact instTy_eq_of_match hvars hm' hag

end Tm

end HOLean
