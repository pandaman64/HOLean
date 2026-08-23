/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Model.Basic
import HOLean.Syntax.Ty

/-!
# Type interpretation

`Ty.denote ρ` is the standard-model universe of a HOL type under a
valuation of schematic type variables.
-/

open ZFSet

namespace HOLean

/-- A valuation of schematic type variables. -/
abbrev TyVal.{u} := Name → ZFSet.{u}

/-- Standard-model interpretation of types. -/
def Ty.denote.{u} (ρ : TyVal.{u}) : Ty → ZFSet.{u}
  | var x => ρ x
  | bool => zfBool
  | ind => omega
  | arrow α β => funs (α.denote ρ) (β.denote ρ)

@[simp] theorem Ty.denote_var (ρ : TyVal) (x : Name) :
    (Ty.var x).denote ρ = ρ x := rfl

@[simp] theorem Ty.denote_bool (ρ : TyVal) : Ty.bool.denote ρ = zfBool := rfl

@[simp] theorem Ty.denote_ind (ρ : TyVal) : Ty.ind.denote ρ = omega := rfl

@[simp] theorem Ty.denote_arrow (ρ : TyVal) (α β : Ty) :
    (α ↝ β).denote ρ = funs (α.denote ρ) (β.denote ρ) := rfl

/-- Push a type substitution through a type valuation.
`INST_TYPE θ` is interpreted by evaluating the original type at `ρ.inst θ`. -/
def TyVal.inst.{u} (ρ : TyVal.{u}) (θ : TySubst) : TyVal.{u} :=
  fun x =>
    match θ.lookup x with
    | some α => α.denote ρ
    | none => ρ x

theorem TyVal.inst_lookup_some {ρ : TyVal} {θ : TySubst} {x : Name} {α : Ty}
    (h : θ.lookup x = some α) : ρ.inst θ x = α.denote ρ := by
  simp [TyVal.inst, h]

theorem TyVal.inst_lookup_none {ρ : TyVal} {θ : TySubst} {x : Name}
    (h : θ.lookup x = none) : ρ.inst θ x = ρ x := by
  simp [TyVal.inst, h]

/-- Type instantiation commutes with denotation. -/
theorem Ty.denote_inst (ρ : TyVal) (θ : TySubst) :
    ∀ α : Ty, (α.inst θ).denote ρ = α.denote (ρ.inst θ)
  | var x => by
    cases h : θ.lookup x with
    | none =>
      simp [Ty.inst, TyVal.inst, h]
    | some α =>
      simp [Ty.inst, TyVal.inst, h]
  | bool => rfl
  | ind => rfl
  | arrow α β => by
    simp [Ty.inst, Ty.denote, Ty.denote_inst ρ θ α, Ty.denote_inst ρ θ β]

theorem Ty.denote_inst_nil (ρ : TyVal) (α : Ty) :
    (α.inst []).denote ρ = α.denote ρ := by
  rw [Ty.inst_nil]

theorem TyVal.inst_nil (ρ : TyVal) : ρ.inst [] = ρ := by
  funext x
  simp [TyVal.inst]

/-- Denotation after composing type substitutions, used to reindex
`FVarVal` when lifting a model along `INST_TYPE`. -/
theorem Ty.denote_inst_comp (ρ : TyVal) (σ θ : TySubst) (α : Ty) :
    α.denote ((ρ.inst σ).inst θ) = α.denote (ρ.inst (θ.comp σ)) := by
  calc
    α.denote ((ρ.inst σ).inst θ)
        = (α.inst θ).denote (ρ.inst σ) := (Ty.denote_inst (ρ.inst σ) θ α).symm
    _   = ((α.inst θ).inst σ).denote ρ := (Ty.denote_inst ρ σ (α.inst θ)).symm
    _   = (α.inst (θ.comp σ)).denote ρ := by rw [Ty.inst_comp]
    _   = α.denote (ρ.inst (θ.comp σ)) := Ty.denote_inst ρ (θ.comp σ) α

end HOLean
