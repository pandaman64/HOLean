/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Syntax.Tm

/-!
# Defined-connective names and term formers

Names and generic types of the Harrison / Andrews connectives, plus the
raw `Tm` formers (`Tm.and`, `Tm.all`, …).  The *defining right-hand
sides* (`Tm.andDef`, …) live in `HOLean.Connective` so they can be
written with `hol_tm` / `hol_prop` without a module cycle:

* this file does not import the elaborator
* the elaborator imports this file (not `Connective`)
* `Connective` imports the elaborator to pretty-print closed definitions
-/

namespace HOLean

def truName : Name := "tru"
def andName : Name := "and"
def impName : Name := "imp"
def allName : Name := "all"
def falsumName : Name := "falsum"
def notName : Name := "not"
def orName : Name := "or"
def exName : Name := "ex"
def oneOneName : Name := "oneOne"
def ontoName : Name := "onto"

def truTy : Ty := .bool
def andTy : Ty := .bool ↝ .bool ↝ .bool
def impTy : Ty := .bool ↝ .bool ↝ .bool
def allTy : Ty := (.var primTyVar ↝ .bool) ↝ .bool
def falsumTy : Ty := .bool
def notTy : Ty := .bool ↝ .bool
def orTy : Ty := .bool ↝ .bool ↝ .bool
def exTy : Ty := (.var primTyVar ↝ .bool) ↝ .bool
def oneOneTy : Ty := (.var primTyVar ↝ .var primTyVarB) ↝ .bool
def ontoTy : Ty := (.var primTyVar ↝ .var primTyVarB) ↝ .bool

theorem allTy_isInstanceOf (α : Ty) :
    allTy.isInstanceOf ((α ↝ .bool) ↝ .bool) :=
  ⟨[(primTyVar, α)], by simp [allTy, primTyVar, Ty.inst, TySubst.lookup]⟩

theorem exTy_isInstanceOf (α : Ty) :
    exTy.isInstanceOf ((α ↝ .bool) ↝ .bool) :=
  ⟨[(primTyVar, α)], by simp [exTy, primTyVar, Ty.inst, TySubst.lookup]⟩

theorem oneOneTy_isInstanceOf (α β : Ty) :
    oneOneTy.isInstanceOf ((α ↝ β) ↝ .bool) :=
  ⟨[(primTyVar, α), (primTyVarB, β)], by
    simp [oneOneTy, primTyVar, primTyVarB, Ty.inst, TySubst.lookup]⟩

theorem ontoTy_isInstanceOf (α β : Ty) :
    ontoTy.isInstanceOf ((α ↝ β) ↝ .bool) :=
  ⟨[(primTyVar, α), (primTyVarB, β)], by
    simp [ontoTy, primTyVar, primTyVarB, Ty.inst, TySubst.lookup]⟩

namespace Tm

/-- The type of a binary boolean combinator, used to define conjunction. -/
def boolCombTy : Ty :=
  .bool ↝ .bool ↝ .bool

theorem boolCombTy_eq : boolCombTy = (.bool ↝ .bool ↝ .bool) := rfl

/-- Object-logic truth constant. -/
def tru : Tm :=
  const truName truTy

/-- Object-logic conjunction. -/
def and (p q : Tm) : Tm :=
  app (app (const andName andTy) p) q

/-- Object-logic implication. -/
def imp (p q : Tm) : Tm :=
  app (app (const impName impTy) p) q

/-- Universal quantification of a predicate `P : α ↝ bool`. -/
def all (α : Ty) (P : Tm) : Tm :=
  app (const allName ((α ↝ .bool) ↝ .bool)) P

/-- Falsity constant. -/
def falsum : Tm :=
  const falsumName falsumTy

/-- Negation. -/
def not (p : Tm) : Tm :=
  app (const notName notTy) p

/-- Disjunction. -/
def or (p q : Tm) : Tm :=
  app (app (const orName orTy) p) q

/-- Existential quantification of a predicate `P : α ↝ bool`. -/
def ex (α : Ty) (P : Tm) : Tm :=
  app (const exName ((α ↝ .bool) ↝ .bool)) P

/-- Injectivity of `f : α ↝ β`. -/
def oneOne (α β : Ty) (f : Tm) : Tm :=
  app (const oneOneName ((α ↝ β) ↝ .bool)) f

/-- Surjectivity of `f : α ↝ β`. -/
def onto (α β : Ty) (f : Tm) : Tm :=
  app (const ontoName ((α ↝ β) ↝ .bool)) f

theorem tru_LC : tru.LC 0 = true := rfl

theorem tru_not_free (x : Name) (α : Ty) : tru.freeIn x α = false := rfl

theorem falsum_LC : falsum.LC 0 = true := rfl

end Tm

end HOLean
