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

end Tm

end HOLean
