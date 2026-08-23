/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Tm

/-!
# Environments

A HOL environment is a constant table plus a set of closed boolean axioms,
in the style of Lean4Lean's `VEnv` (`constants` + `defeqs`).  HOL Light has
no δ-reduction, so there is no independent definitional equality: a
definition is the axiom `⊢ c = t` and unfolding is `EQ_MP` / rewriting.

```
Env  ≔  constants : Name → Option Ty     -- generic types
      × axioms    : Tm → Prop            -- closed booleans
```

`HasType` reads only `constants`, never `axioms`.  That breaks the cycle
between typing the primitive axioms and installing them in the initial
environment: `holCore` has the primitive constants and no axioms;
`HOLAxiom` is typed against `holCore`; `holEnv` is `holCore` plus those
axioms.

User definitions grow the environment (`addConst` / `addAxiom` / `addDef`).
Connectives stay as Lean term formers in this slice; type-level
`new_basic_type_definition` is later.
-/

namespace HOLean

/-- A HOL signature: generic types of constants, plus postulated sentences. -/
structure Env where
  /-- Generic type of each declared constant, if any. -/
  constants : Name → Option Ty
  /-- Postulated closed boolean terms. -/
  axioms : Tm → Prop

namespace Env

/-- `env` is a sub-environment of `env'`: every constant and axiom is kept. -/
structure LE (env env' : Env) : Prop where
  constants : ∀ n ty, env.constants n = some ty → env'.constants n = some ty
  axioms : ∀ ax, env.axioms ax → env'.axioms ax

theorem LE.refl (env : Env) : env.LE env :=
  ⟨fun _ _ h => h, fun _ h => h⟩

theorem LE.trans {e₁ e₂ e₃ : Env} (h₁ : e₁.LE e₂) (h₂ : e₂.LE e₃) : e₁.LE e₃ :=
  ⟨fun n ty h => h₂.constants n ty (h₁.constants n ty h),
   fun ax h => h₂.axioms ax (h₁.axioms ax h)⟩

/-- The environment has object-logic equality. -/
class HasEq (env : Env) : Prop where
  eq_const : env.constants eqName = some eqTy

/-- The environment has Hilbert choice. -/
class HasSelect (env : Env) : Prop where
  select_const : env.constants selectName = some selectTy

/-- The environment has both primitive constants. -/
class HasPrims (env : Env) extends HasEq env, HasSelect env

/-- Declare a constant with generic type `ty`. -/
def addConst (env : Env) (n : Name) (ty : Ty) : Env where
  constants := fun m => if m = n then some ty else env.constants m
  axioms := env.axioms

/-- Postulate a closed boolean. -/
def addAxiom (env : Env) (ax : Tm) : Env where
  constants := env.constants
  axioms := fun t => t = ax ∨ env.axioms t

/-- Definitional extension: add `n : ty` and the axiom `n = rhs`. -/
def addDef (env : Env) (n : Name) (ty : Ty) (rhs : Tm) : Env :=
  (env.addConst n ty).addAxiom (Tm.mkEq ty (.const n ty) rhs)

@[simp] theorem addConst_self (env : Env) (n : Name) (ty : Ty) :
    (env.addConst n ty).constants n = some ty := by
  simp [addConst]

theorem addConst_of_ne (env : Env) {n m : Name} (ty : Ty) (h : m ≠ n) :
    (env.addConst n ty).constants m = env.constants m := by
  simp [addConst, h]

@[simp] theorem addAxiom_constants (env : Env) (ax : Tm) :
    (env.addAxiom ax).constants = env.constants := rfl

theorem addAxiom_self (env : Env) (ax : Tm) :
    (env.addAxiom ax).axioms ax :=
  Or.inl rfl

theorem LE.addConst_of_fresh {env : Env} {n : Name} {ty : Ty}
    (h : env.constants n = none) :
    env.LE (env.addConst n ty) :=
  ⟨fun m τ hm => by
      by_cases hmn : m = n
      · subst hmn
        simp [h] at hm
      · simpa [addConst, hmn] using hm,
   fun ax hax => hax⟩

theorem LE.addAxiom (env : Env) (ax : Tm) : env.LE (env.addAxiom ax) :=
  ⟨fun _ _ h => h, fun _ h => Or.inr h⟩

theorem LE.addDef_of_fresh {env : Env} {n : Name} {ty : Ty} {rhs : Tm}
    (h : env.constants n = none) :
    env.LE (env.addDef n ty rhs) :=
  (LE.addConst_of_fresh h).trans (LE.addAxiom _ _)

theorem HasEq.addConst {env : Env} [HasEq env] {n : Name} {ty : Ty}
    (hn : n ≠ eqName) : HasEq (env.addConst n ty) where
  eq_const := by
    change (if eqName = n then some ty else env.constants eqName) = some eqTy
    rw [if_neg hn.symm]
    exact HasEq.eq_const (env := env)

theorem HasSelect.addConst {env : Env} [HasSelect env] {n : Name} {ty : Ty}
    (hn : n ≠ selectName) : HasSelect (env.addConst n ty) where
  select_const := by
    change (if selectName = n then some ty else env.constants selectName) = some selectTy
    rw [if_neg hn.symm]
    exact HasSelect.select_const (env := env)

theorem HasEq.addAxiom (env : Env) [HasEq env] (ax : Tm) : HasEq (env.addAxiom ax) where
  eq_const := HasEq.eq_const (env := env)

theorem HasSelect.addAxiom (env : Env) [HasSelect env] (ax : Tm) :
    HasSelect (env.addAxiom ax) where
  select_const := HasSelect.select_const (env := env)

theorem HasEq.addDef {env : Env} [HasEq env] {n : Name} {ty : Ty} {rhs : Tm}
    (hn : n ≠ eqName) : HasEq (env.addDef n ty rhs) :=
  haveI := HasEq.addConst (env := env) (n := n) (ty := ty) hn
  HasEq.addAxiom _ _

end Env

/-- Primitive constants, no axioms.  Used to type the HOL axiom schemas
without referring to `holEnv` itself. -/
def holCore : Env where
  constants := holConstants
  axioms := fun _ => False

instance : Env.HasEq holCore where
  eq_const := holConstants_eq

instance : Env.HasSelect holCore where
  select_const := holConstants_select

instance : Env.HasPrims holCore where

@[simp] theorem holCore_constants : holCore.constants = holConstants := rfl

end HOLean
