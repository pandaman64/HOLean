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
* constants (`const`) — a primitive plus its type-argument
* application and λ-abstraction

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
  /-- Primitive constant instantiated at a type argument. -/
  | const : Const → Ty → Tm
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
@[simp] theorem instTy_const (θ : TySubst) (c : Const) (α : Ty) :
    (const c α).instTy θ = const c (α.inst θ) := rfl
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

@[simp] theorem substFvar_const (x : Name) (α : Ty) (u : Tm) (c : Const) (β : Ty) :
    (const c β).substFvar x α u = const c β := rfl

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

/-- `s = t` at type `α`, i.e. `(=)[α] s t`. -/
def mkEq (α : Ty) (s t : Tm) : Tm :=
  app (app (const .eq α) s) t

@[simp] theorem mkEq_eq (α : Ty) (s t : Tm) :
    mkEq α s t = app (app (const .eq α) s) t := rfl

/-- Destructor for equations. -/
def destEq : Tm → Option (Ty × Tm × Tm)
  | app (app (const .eq α) s) t => some (α, s, t)
  | _ => none

@[simp] theorem destEq_mkEq (α : Ty) (s t : Tm) :
    destEq (mkEq α s t) = some (α, s, t) := rfl

/-- Schematic type variables occurring in a term. -/
def tyvars : Tm → List Name
  | bvar _ => []
  | fvar _ α => α.tyvars
  | const _ α => α.tyvars
  | app f a => f.tyvars ++ a.tyvars.filter (· ∉ f.tyvars)
  | lam α t => α.tyvars ++ t.tyvars.filter (· ∉ α.tyvars)

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
@[simp] theorem LC_const (c : Const) (α : Ty) (n : Nat) : (const c α).LC n = true := rfl
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

end Tm

end HOLean
