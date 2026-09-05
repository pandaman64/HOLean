/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Tm

/-!
# Environments

A HOL environment is a constant table plus a list of closed boolean axioms,
in the style of Lean4Lean's `VEnv` (`constants` + `defeqs`).  HOL Light has
no δ-reduction, so there is no independent definitional equality: a
definition is the axiom `⊢ c = t` and unfolding is `EQ_MP` / rewriting.

```
Env  ≔  constants : List (Name × Ty)     -- generic types (first match wins)
      × axioms    : List Tm              -- closed booleans
```

`HasType` reads only `constants` (via `Env.lookup`), never `axioms`.  That
breaks the cycle between typing axioms and installing them: `holCore` has
the primitive constants and no axioms; `holLogic` is the definitional chain
of connectives; `HOLAxiom` is typed against `holLogic`; `holEnv` is
`holLogic` plus the three closed HOL axioms.

User definitions grow the environment (`addConst` / `addAxiom` / `addDef`).
Logical connectives are definitional extensions of `holCore` (`holLogic`).
Type-level `new_basic_type_definition` is later.

An environment is **well-formed** (`Env.WF`, after `HasType`) when every
axiom is a closed boolean in that signature.  The constant table needs no
separate check: every `Ty` is a valid generic type.
-/

namespace HOLean

/-- A HOL signature: generic types of constants, plus postulated sentences. -/
structure Env where
  /-- Generic type of each declared constant (first match wins). -/
  constants : List (Name × Ty)
  /-- Postulated sentences.  `Env.WF` requires each to be a closed boolean
  in this signature (`HasType env [] p .bool`). -/
  axioms : List Tm

namespace Env

/-- Look up the generic type of constant `n`. -/
abbrev lookup (env : Env) (n : Name) : Option Ty :=
  ConstTable.lookup env.constants n

/-- `env` is a sub-environment of `env'`: every constant and axiom is kept. -/
structure LE (env env' : Env) : Prop where
  constants : ∀ n ty, env.lookup n = some ty → env'.lookup n = some ty
  axioms : ∀ ax, ax ∈ env.axioms → ax ∈ env'.axioms

theorem LE.refl (env : Env) : env.LE env :=
  ⟨fun _ _ h => h, fun _ h => h⟩

theorem LE.trans {e₁ e₂ e₃ : Env} (h₁ : e₁.LE e₂) (h₂ : e₂.LE e₃) : e₁.LE e₃ :=
  ⟨fun n ty h => h₂.constants n ty (h₁.constants n ty h),
   fun ax h => h₂.axioms ax (h₁.axioms ax h)⟩

/-- The environment has object-logic equality. -/
class HasEq (env : Env) : Prop where
  eq_const : env.lookup eqName = some eqTy

/-- The environment has Hilbert choice. -/
class HasSelect (env : Env) : Prop where
  select_const : env.lookup selectName = some selectTy

/-- The environment has both primitive constants. -/
class HasPrims (env : Env) extends HasEq env, HasSelect env

/-- Declare a constant with generic type `ty`. -/
def addConst (env : Env) (n : Name) (ty : Ty) : Env where
  constants := (n, ty) :: env.constants
  axioms := env.axioms

/-- Postulate a closed boolean. -/
def addAxiom (env : Env) (ax : Tm) : Env where
  constants := env.constants
  axioms := ax :: env.axioms

/-- Definitional extension: add `n : ty` and the axiom `n = rhs`. -/
def addDef (env : Env) (n : Name) (ty : Ty) (rhs : Tm) : Env :=
  (env.addConst n ty).addAxiom (Tm.mkEq ty (.const n ty) rhs)

@[simp] theorem addConst_self (env : Env) (n : Name) (ty : Ty) :
    (env.addConst n ty).lookup n = some ty := by
  simp [addConst, lookup, ConstTable.lookup]

theorem addConst_of_ne (env : Env) {n m : Name} (ty : Ty) (h : m ≠ n) :
    (env.addConst n ty).lookup m = env.lookup m := by
  have h' : n ≠ m := Ne.symm h
  simp [addConst, lookup, ConstTable.lookup, h']

@[simp] theorem addAxiom_constants (env : Env) (ax : Tm) :
    (env.addAxiom ax).constants = env.constants := rfl

@[simp] theorem addAxiom_lookup (env : Env) (ax : Tm) (n : Name) :
    (env.addAxiom ax).lookup n = env.lookup n := rfl

theorem addAxiom_self (env : Env) (ax : Tm) :
    ax ∈ (env.addAxiom ax).axioms :=
  List.Mem.head _

theorem LE.addConst_of_fresh {env : Env} {n : Name} {ty : Ty}
    (h : env.lookup n = none) :
    env.LE (env.addConst n ty) :=
  ⟨fun m τ hm => by
      by_cases hmn : m = n
      · subst hmn
        rw [h] at hm
        cases hm
      · rwa [addConst_of_ne env ty hmn],
   fun ax hax => by simpa [addConst] using hax⟩

theorem LE.addAxiom (env : Env) (ax : Tm) : env.LE (env.addAxiom ax) :=
  ⟨fun _ _ h => h, fun _ h => List.Mem.tail _ h⟩

theorem LE.addDef_of_fresh {env : Env} {n : Name} {ty : Ty} {rhs : Tm}
    (h : env.lookup n = none) :
    env.LE (env.addDef n ty rhs) :=
  (LE.addConst_of_fresh h).trans (LE.addAxiom _ _)

theorem HasEq.addConst {env : Env} [HasEq env] {n : Name} {ty : Ty}
    (hn : n ≠ eqName) : HasEq (env.addConst n ty) where
  eq_const := by
    rw [addConst_of_ne env ty (Ne.symm hn)]
    exact HasEq.eq_const (env := env)

theorem HasSelect.addConst {env : Env} [HasSelect env] {n : Name} {ty : Ty}
    (hn : n ≠ selectName) : HasSelect (env.addConst n ty) where
  select_const := by
    rw [addConst_of_ne env ty (Ne.symm hn)]
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

theorem HasSelect.addDef {env : Env} [HasSelect env] {n : Name} {ty : Ty} {rhs : Tm}
    (hn : n ≠ selectName) : HasSelect (env.addDef n ty rhs) :=
  haveI := HasSelect.addConst (env := env) (n := n) (ty := ty) hn
  HasSelect.addAxiom _ _

@[simp] theorem addDef_constants_self (env : Env) (n : Name) (ty : Ty) (rhs : Tm) :
    (env.addDef n ty rhs).lookup n = some ty := by
  simp [addDef, addAxiom, addConst, lookup, ConstTable.lookup]

theorem addDef_constants_of_ne (env : Env) {n m : Name} (ty : Ty) (rhs : Tm)
    (h : m ≠ n) :
    (env.addDef n ty rhs).lookup m = env.lookup m := by
  have h' : n ≠ m := Ne.symm h
  simp [addDef, addAxiom, addConst, lookup, ConstTable.lookup, h']

theorem addDef_axioms_self (env : Env) (n : Name) (ty : Ty) (rhs : Tm) :
    Tm.mkEq ty (.const n ty) rhs ∈ (env.addDef n ty rhs).axioms :=
  addAxiom_self _ _

theorem addDef_axioms_of {env : Env} {n : Name} {ty : Ty} {rhs ax : Tm}
    (h : ax ∈ env.axioms) :
    ax ∈ (env.addDef n ty rhs).axioms :=
  List.Mem.tail _ (by exact h)

theorem addAxiom_axioms_of {env : Env} (ax p : Tm) (h : p ∈ env.axioms) :
    p ∈ (env.addAxiom ax).axioms :=
  List.Mem.tail _ h

end Env

/-- Primitive constants, no axioms.  The connective chain (`holLogic`) and
the three closed HOL axioms (`HOLAxiom`) are layered on top of this. -/
def holCore : Env where
  constants := holConstants
  axioms := []

instance : Env.HasEq holCore where
  eq_const := by simp [Env.lookup, holCore, holConstants_eq]

instance : Env.HasSelect holCore where
  select_const := by simp [Env.lookup, holCore, holConstants_select]

instance : Env.HasPrims holCore where

@[simp] theorem holCore_constants : holCore.constants = holConstants := rfl

@[simp] theorem holCore_lookup (n : Name) :
    holCore.lookup n = ConstTable.lookup holConstants n := rfl

end HOLean
