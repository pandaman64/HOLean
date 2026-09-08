/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Prove.Basic

/-!
# Verified type checking

`infer` / `checkType` return `HasType` proofs on success, via
`HasType.of_infer` on a dependent match — not an elaborator-built
constructor tree.
-/

namespace HOLean
namespace Prove

variable {env : Env}

/-- Infer `tm`’s type, or fail. -/
def infer (Γ : List Ty) (tm : Tm) :
    ProveM env (Σ ty : Ty, Proof (HasType env Γ tm ty)) := do
  match h : tm.infer env Γ with
  | some ty => return ⟨ty, ⟨HasType.of_infer h⟩⟩
  | none => ProveM.throw s!"not well-typed: {repr tm}"

/-- Check `tm` against an expected type. -/
def checkType (Γ : List Ty) (tm : Tm) (ty : Ty) :
    ProveM env (Proof (HasType env Γ tm ty)) := do
  let ⟨ty', ht⟩ ← infer Γ tm
  if h : ty' = ty then
    return ⟨h ▸ ht.down⟩
  else
    ProveM.throw s!"expected type {repr ty}, got {repr ty'}"

def checkBool (Γ : List Ty) (t : Tm) :
    ProveM env (Proof (HasType env Γ t .bool)) :=
  checkType Γ t .bool

def checkClosed (t : Tm) : ProveM env (Proof (t.LC 0 = true)) :=
  if h : t.LC 0 = true then
    return ⟨h⟩
  else
    ProveM.throw s!"not locally closed: {repr t}"

def checkFreshConst (n : Name) : ProveM env (Proof (env.lookup n = none)) :=
  if h : env.lookup n = none then
    return ⟨h⟩
  else
    ProveM.throw s!"constant `{n}` is already declared"

def checkMemAxioms (p : Tm) : ProveM env (Proof (p ∈ env.axioms)) :=
  if h : p ∈ env.axioms then
    return ⟨h⟩
  else
    ProveM.throw s!"not an environment axiom: {repr p}"

def checkFreshHyps (x : Name) (α : Ty) :
    (Γ : List Tm) → ProveM env (Proof (∀ p ∈ Γ, p.freeIn x α = false))
  | [] =>
    return ⟨by intro p hp; cases hp⟩
  | q :: qs => do
    if hf : q.freeIn x α = false then
      let ⟨ih⟩ ← checkFreshHyps x α qs
      return ⟨by
        intro p hp
        cases hp with
        | head => exact hf
        | tail _ hp => exact ih p hp⟩
    else
      ProveM.throw s!"ABS/GEN: variable {x} is free in a hypothesis"

def checkNotMem (p : Tm) :
    (Γ : List Tm) → ProveM env (Proof (p ∉ Γ))
  | [] =>
    return ⟨by intro hp; cases hp⟩
  | q :: qs => do
    if heq : q = p then
      ProveM.throw s!"unexpected hypothesis {repr p}"
    else
      let ⟨ih⟩ ← checkNotMem p qs
      return ⟨by
        intro hp
        cases hp with
        | head => exact heq rfl
        | tail _ hp => exact ih hp⟩

def checkNotFree : (t : Tm) → ProveM env (Proof (∀ x α, t.freeIn x α = false))
  | .bvar _ => return ⟨fun _ _ => rfl⟩
  | .fvar y β => ProveM.throw s!"term has free variable {y}"
  | .const _ _ => return ⟨fun _ _ => rfl⟩
  | .app f a => do
    let ⟨hf⟩ ← checkNotFree f
    let ⟨ha⟩ ← checkNotFree a
    return ⟨fun x α => by simp [Tm.freeIn, hf x α, ha x α]⟩
  | .lam _ t => do
    let ⟨ht⟩ ← checkNotFree t
    return ⟨fun x α => by simp [Tm.freeIn, ht x α]⟩

theorem substOk_nil {env : Env} : Tm.Subst.Ok env ([] : Tm.Subst) := by
  intro y γ v hv
  simp [Tm.Subst.lookup] at hv

theorem substOk_cons {env : Env} {x : Name} {α : Ty} {u : Tm} {rest : Tm.Subst}
    (hu : HasType env [] u α) (hrest : rest.Ok env) :
    Tm.Subst.Ok env ((x, α, u) :: rest) := by
  intro y γ v hv
  simp [Tm.Subst.lookup] at hv
  split at hv
  · next heq =>
    obtain ⟨rfl, rfl⟩ := heq
    simp at hv
    exact hv ▸ hu
  · exact hrest y γ v hv

def checkSubst : (σ : Tm.Subst) → ProveM env (Proof (σ.Ok env))
  | [] => return ⟨substOk_nil⟩
  | (_x, α, u) :: rest => do
    let ⟨hu⟩ ← checkType [] u α
    let ⟨hrest⟩ ← checkSubst rest
    return ⟨substOk_cons hu hrest⟩

def checkTyvars (ty : Ty) (rhs : Tm) :
    ProveM env (Proof (∀ x ∈ rhs.tyvars, x ∈ ty.tyvars)) :=
  if h : rhs.tyvars.all (fun x => decide (x ∈ ty.tyvars)) = true then
    return ⟨by
      intro x hx
      have hx' := (List.all_eq_true.1 h) x hx
      simpa using hx'⟩
  else
    ProveM.throw "type variables of the RHS must occur in the declared type"

def checkNameNotReserved (n : Name) :
    ProveM env (Proof (nameNotInConnectiveAndPrim n)) :=
  if h : ∀ m ∈ connectiveAndPrimNames, n ≠ m then
    return ⟨h⟩
  else
    ProveM.throw s!"name `{n}` is reserved"

end Prove
end HOLean
