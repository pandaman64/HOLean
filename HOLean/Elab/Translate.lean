/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Syntax.Logic
import HOLean.Elab.State

/-!
# Lean.Expr → HOL

Lean's elaborator is reused as a frontend: a Lean4-like term, type, or
proposition is elaborated to a `Lean.Expr`, then this module walks that
expression and emits `Ty` / `Tm`.

Classification is by **sort**:

* `e : Prop` (sort 0) is a HOL proposition — a term of type `bool`
* `e : Type u` is a HOL type, provided it is a *simple* type
* otherwise `e` is a HOL term of the translated type of `e`

Dependent types are rejected: a `∀ (x : α), β` whose body has sort `Type`
and mentions `x` is not a HOL type.  A `∀ (x : α), p` whose body has sort
`Prop` is a universal quantifier (or an implication, when `α : Prop` and
`p` does not mention the proof).

`Type`-binders (`∀ α : Type, …`, implicit `{α}`) are *schematic* type
variables, not System F type lambdas: they are opened as free type
variables and do not appear as `Tm.lam`.
-/

open Lean Meta

namespace HOLean

/-- Lean stand-in for the HOL type of individuals.  `Nat` is also accepted. -/
opaque Ind : Type

/-- Lean stand-in for HOL `ONE_ONE`. -/
opaque oneOne {α β : Type} (f : α → β) : Prop

/-- Lean stand-in for HOL `ONTO`. -/
opaque onto {α β : Type} (f : α → β) : Prop

deriving instance ToExpr for Ty
deriving instance ToExpr for Tm

end HOLean

namespace HOLean.Elab

/-- Strip hygiene and render a Lean name as a HOL `Name`. -/
def holName (n : Lean.Name) : HOLean.Name :=
  let n := n.eraseMacroScopes
  match n with
  | .anonymous => "_"
  | .str .anonymous s => s
  | _ => n.toString

/-- `Sort (u+1)` / `Type u` — a binder for a schematic type variable. -/
def isTyVarSort (e : Expr) : MetaM Bool := do
  let e ← whnf e
  return e.isSort && !e.isProp

/-- Prepare an elaborated expression for translation. -/
def ready (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  if e.hasExprMVar then
    throwError "HOLean: expression still has metavariables{indentExpr e}"
  return e

mutual

/-- Apply a HOL head to Lean arguments, each translated as a term. -/
partial def apps (head : Tm) (args : Array Expr) : MetaM Tm :=
  args.foldlM (init := head) fun t a =>
    return Tm.app t (← exprToTm a)

/-- Translate a Lean type (`e : Type u` or `e = Prop`) to a HOL type. -/
partial def exprToTy (e : Expr) : MetaM Ty := do
  let e ← ready e
  let e ← whnf e
  match e with
  | .sort l =>
    if l.isZero then
      return .bool
    else
      throwError "HOLean: `{e}` is a universe, not a HOL type \
        (use `Prop`/`Bool` for bool, `Nat`/`Ind` for ind, or a type variable)"
  | .fvar id =>
    let decl ← id.getDecl
    let ty ← whnf decl.type
    unless ty.isSort do
      throwError "HOLean: `{decl.userName}` is not a type"
    if ty.isProp then
      throwError "HOLean: proposition `{decl.userName}` is not a HOL type \
        (it is a term of type bool)"
    return .var (holName decl.userName)
  | .const n _ =>
    if n == `Prop || n == ``Bool then
      return .bool
    else if n == ``Nat || n == ``HOLean.Ind then
      return .ind
    else
      throwError "HOLean: unknown type constant `{n}`"
  | .forallE n α body bi =>
    if bi.isInstImplicit then
      throwError "HOLean: type-class binders are not allowed"
    if (← isTyVarSort α) then
      -- Schematic type variable, not a dependent type.
      withLocalDecl n bi α fun x =>
        exprToTy (body.instantiate1 x)
    else
      withLocalDecl n bi α fun x => do
        let body' := body.instantiate1 x
        if body'.containsFVar x.fvarId! then
          throwError "HOLean: dependent type is not a HOL type{indentExpr e}"
        return (← exprToTy α) ↝ (← exprToTy body')
  | .letE _ _ v b _ =>
    exprToTy (b.instantiate1 v)
  | .mdata _ e =>
    exprToTy e
  | _ =>
    throwError "HOLean: not a simple type{indentExpr e}"

/-- Known Lean constants that denote HOL primitives or connectives. -/
partial def translateConst (n : Lean.Name) (args : Array Expr) : MetaM (Option Tm) := do
  match n with
  | ``True | ``Bool.true =>
    if args.isEmpty then return some Tm.tru else return none
  | ``False | ``Bool.false =>
    if args.isEmpty then return some Tm.falsum else return none
  | ``And | ``Bool.and =>
    some <$> apps (.const andName andTy) args
  | ``Or | ``Bool.or =>
    some <$> apps (.const orName orTy) args
  | ``Not | ``Bool.not =>
    some <$> apps (.const notName notTy) args
  | ``Iff =>
    some <$> apps (Tm.eqConst .bool) args
  | ``Eq =>
    if args.isEmpty then
      throwError "HOLean: `Eq` needs a type argument"
    else
      let α ← exprToTy args[0]!
      some <$> apps (Tm.eqConst α) args[1:]
  | ``Ne =>
    match args with
    | #[α, x, y] =>
      return some (Tm.not (Tm.mkEq (← exprToTy α) (← exprToTm x) (← exprToTm y)))
    | _ => return none
  | ``Exists =>
    if args.isEmpty then
      throwError "HOLean: `Exists` needs a type argument"
    else
      let α ← exprToTy args[0]!
      some <$> apps (.const exName ((α ↝ .bool) ↝ .bool)) args[1:]
  | ``Classical.epsilon =>
    match args with
    | #[α, _inst, p] =>
      return some (Tm.app (Tm.selectConst (← exprToTy α)) (← exprToTm p))
    | #[α, _inst] =>
      return some (Tm.selectConst (← exprToTy α))
    | _ => return none
  | ``id =>
    match args with
    | #[α] =>
      let α ← exprToTy α
      return some (.lam α (.bvar 0))
    | #[_α, x] => some <$> exprToTm x
    | _ => return none
  | ``HOLean.oneOne =>
    match args with
    | #[α, β, f] =>
      return some (Tm.oneOne (← exprToTy α) (← exprToTy β) (← exprToTm f))
    | #[α, β] =>
      return some (.const oneOneName (((← exprToTy α) ↝ (← exprToTy β)) ↝ .bool))
    | _ => return none
  | ``HOLean.onto =>
    match args with
    | #[α, β, f] =>
      return some (Tm.onto (← exprToTy α) (← exprToTy β) (← exprToTm f))
    | #[α, β] =>
      return some (.const ontoName (((← exprToTy α) ↝ (← exprToTy β)) ↝ .bool))
    | _ => return none
  | n =>
    if let some (holName, gen) := findUserDef? (← getEnv) n then
      some <$> applyUserConst holName gen args
    else if args.isEmpty then
      if let some stmt := findUserThmByLean? (← getEnv) n then
        return some stmt
      else
        return none
    else
      return none

/-- Apply a user `hdef` constant, instantiating schematic type variables
from Lean type arguments and from the types of term arguments. -/
partial def applyUserConst (holName : HOLean.Name) (gen : Ty) (args : Array Expr) :
    MetaM Tm := do
  let mut θ : TySubst := []
  let mut targs : Array Expr := #[]
  for a in args do
    let aTy ← whnf (← inferType a)
    if aTy.isSort && !aTy.isProp then
      let tvs := gen.tyvars.filter fun x => (θ.lookup x).isNone
      if tvs.isEmpty then
        throwError "HOLean: extra type argument{indentExpr a}"
      let τ ← exprToTy a
      θ := θ ++ [(tvs[0]!, τ)]
    else
      targs := targs.push a
  let mut rest := gen.inst θ
  for a in targs do
    match rest with
    | .arrow α β =>
      let aTy ← exprToTy (← inferType a)
      match α.matchTy aTy θ with
      | some θ' =>
        θ := θ'
        rest := β.inst θ
      | none =>
        throwError "HOLean: cannot instantiate `{holName}` at argument{indentExpr a}"
    | _ =>
      throwError "HOLean: too many arguments to `{holName}`"
  apps (.const holName (gen.inst θ)) targs

/-- Translate a Lean term or proposition to a HOL term. -/
partial def exprToTm (e : Expr) : MetaM Tm := do
  let e ← ready e
  match e with
  | .mdata _ e =>
    exprToTm e
  | .fvar id =>
    let decl ← id.getDecl
    let ty ← whnf decl.type
    if ty.isSort && !ty.isProp then
      throwError "HOLean: type variable `{decl.userName}` is a HOL type, not a term"
    return .fvar (holName decl.userName) (← exprToTy decl.type)
  | .bvar i =>
    return .bvar i
  | .sort l =>
    throwError "HOLean: universe {Expr.sort l} is a type, not a term (use `hol_ty%`)"
  | .lam n α body bi =>
    if bi.isInstImplicit then
      throwError "HOLean: type-class binders are not allowed"
    if (← isTyVarSort α) then
      -- Schematic type binder (`fun {α : Type} => …`).
      withLocalDecl n bi α fun x =>
        exprToTm (body.instantiate1 x)
    else
      withLocalDecl n bi α fun x => do
        let αT ← exprToTy α
        let t ← exprToTm (body.instantiate1 x)
        return t.abstract (holName (← x.fvarId!.getUserName)) αT
  | .forallE n α body bi =>
    if bi.isInstImplicit then
      throwError "HOLean: type-class binders are not allowed"
    if (← isTyVarSort α) then
      -- Schematic `∀ α : Type, p` — open `α` and translate `p`.
      withLocalDecl n bi α fun x =>
        exprToTm (body.instantiate1 x)
    else
      withLocalDecl n bi α fun x => do
        let body' := body.instantiate1 x
        unless (← Meta.isProp body') do
          throwError "HOLean: this Π is a type former, not a HOL term{indentExpr e}"
        if ← Meta.isProp α then
          -- Implication `p → q`.  A body that mentions the proof is dependent.
          if body'.containsFVar x.fvarId! then
            throwError "HOLean: dependent implication is not a HOL term{indentExpr e}"
          return Tm.imp (← exprToTm α) (← exprToTm body')
        else
          let αT ← exprToTy α
          let t ← exprToTm body'
          return Tm.all αT (t.abstract (holName (← x.fvarId!.getUserName)) αT)
  | .letE _ _ v b _ =>
    exprToTm (b.instantiate1 v)
  | .const .. | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
      if let some t ← translateConst n args then
        return t
      throwError "HOLean: unknown constant `{n}`"
    | _ =>
      let mut t ← exprToTm fn
      for a in args do
        let aTy ← whnf (← inferType a)
        if aTy.isSort && !aTy.isProp then
          throwError "HOLean: type application is not allowed \
            (polymorphism is schematic){indentExpr a}"
        t := Tm.app t (← exprToTm a)
      return t
  | .mvar .. =>
    throwError "HOLean: unassigned metavariable{indentExpr e}"
  | .lit .. =>
    throwError "HOLean: literals are not HOL terms{indentExpr e}"
  | .proj .. =>
    throwError "HOLean: structure projections are not HOL terms{indentExpr e}"

end

end HOLean.Elab
