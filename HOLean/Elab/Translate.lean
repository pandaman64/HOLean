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

Antiquotation `⌜t⌝` (see `HOLean.Elab.Term`) inserts a `Tm` or `Ty`
value into the Lean stand-in.  The translator replaces `holTmQuote` /
`holTyQuote` with that value, so `hol_prop(⌜p⌝ ∧ True)` elaborates to
`Tm.and p Tm.tru`.
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

/-- Intermediate stand-in for `⌜t⌝` when `t : Tm`.  The HOL translator
replaces this with `t`; it should not appear in elaborated output. -/
axiom holTmQuote (α : Sort u) (t : Tm) : α

/-- Wrapper used when `⌜t⌝` has no expected Lean type.  `CoeFun` lets Lean
infer a function type for `⌜f⌝ x` instead of the elaborator picking one. -/
structure HolQuoted where
  tm : Tm

noncomputable instance : CoeFun HolQuoted (fun _ => ∀ {α : Sort u} {β : Sort v}, α → β) where
  coe q := holTmQuote (∀ {α : Sort u} {β : Sort v}, α → β) q.tm

/-- Intermediate stand-in for `⌜α⌝` when `α : Ty`. -/
opaque holTyQuote (α : Ty) : Type

/-- A HOL type, or a Lean expression of type `Ty` (an antiquotation). -/
inductive TyQ where
  | val : Ty → TyQ
  | expr : Expr → TyQ

/-- Quoted HOL term.  `val` is a fully known tree (no antiquotations).
`splice` is `⌜t⌝`.  `app'` / `lam'` / `fvar'` / `const'` keep structure so
that abstracting a Lean binder does not `close` inside a splice. -/
inductive TmQ where
  | val : Tm → TmQ
  | splice : Expr → TmQ
  | app' : TmQ → TmQ → TmQ
  | lam' : TyQ → TmQ → TmQ
  | fvar' : HOLean.Name → TyQ → TmQ
  | const' : HOLean.Name → TyQ → TmQ

def TyQ.toExpr : TyQ → Expr
  | .val α => Lean.toExpr α
  | .expr e => e

def TyQ.beq : TyQ → TyQ → Bool
  | .val α, .val β => α == β
  | .expr a, .expr b => a == b
  | _, _ => false

/-- `t` and any extra Lean arguments (`⌜f⌝ x y` → splice `f` applied to `x`, `y`). -/
def destHolTmQuote? (e : Expr) : Option (Expr × Array Expr) :=
  if e.isAppOf ``holTmQuote then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      some (args[1]!, args.extract 2 args.size)
    else none
  else none

/-- Peel `holTmQuote` / `HolQuoted` / `CoeFun` so a splice is visible. -/
partial def destTmSplice? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let e := (← instantiateMVars e).consumeMData
  if let some r := destHolTmQuote? e then
    return some r
  if e.isAppOfArity ``HolQuoted.mk 1 then
    return some (e.appArg!, #[])
  if e.isAppOfArity ``HolQuoted.tm 1 then
    return some (e.appArg!, #[])
  if e.isAppOf ``CoeFun.coe then
    let args := e.getAppArgs
    if args.size ≥ 4 then
      if let some (t, extras) ← destTmSplice? args[3]! then
        return some (t, extras ++ args.extract 4 args.size)
    return none
  let e' ← whnf e
  if e' == e then return none
  destTmSplice? e'

def isHolTyQuote? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``holTyQuote 1 then some e.appArg! else none

def decodeString (e : Expr) : MetaM String := do
  let e ← whnf e
  match e with
  | .lit (.strVal s) => return s
  | _ => throwError "HOLean: expected a string literal{indentExpr e}"

def decodeNat (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e.nat? with
  | some n => return n
  | none => throwError "HOLean: expected a nat literal{indentExpr e}"

partial def decodeTy (e : Expr) : MetaM Ty := do
  let e ← whnf e
  if e.isConstOf ``Ty.bool then
    return .bool
  if e.isConstOf ``Ty.ind then
    return .ind
  if e.isAppOfArity ``Ty.var 1 then
    return .var (← decodeString (e.getArg! 0))
  if e.isAppOfArity ``Ty.arrow 2 then
    return (← decodeTy (e.getArg! 0)) ↝ (← decodeTy (e.getArg! 1))
  throwError "HOLean: expected a closed `Ty`{indentExpr e}"

partial def decodeTm (e : Expr) : MetaM Tm := do
  let e ← whnf e
  if e.isAppOfArity ``Tm.bvar 1 then
    return .bvar (← decodeNat (e.getArg! 0))
  if e.isAppOfArity ``Tm.fvar 2 then
    return .fvar (← decodeString (e.getArg! 0)) (← decodeTy (e.getArg! 1))
  if e.isAppOfArity ``Tm.const 2 then
    return .const (← decodeString (e.getArg! 0)) (← decodeTy (e.getArg! 1))
  if e.isAppOfArity ``Tm.app 2 then
    return .app (← decodeTm (e.getArg! 0)) (← decodeTm (e.getArg! 1))
  if e.isAppOfArity ``Tm.lam 2 then
    return .lam (← decodeTy (e.getArg! 0)) (← decodeTm (e.getArg! 1))
  throwError "HOLean: expected a closed `Tm`{indentExpr e}"

def TyQ.force : TyQ → MetaM Ty
  | .val α => return α
  | .expr e => decodeTy e

def TyQ.arrow : TyQ → TyQ → TyQ
  | .val α, .val β => .val (α ↝ β)
  | α, β => .expr (mkApp2 (mkConst ``Ty.arrow) α.toExpr β.toExpr)

def TmQ.app : TmQ → TmQ → TmQ
  | .val f, .val a => .val (Tm.app f a)
  | f, a => .app' f a

def TmQ.lam : TyQ → TmQ → TmQ
  | .val α, .val t => .val (.lam α t)
  | α, t => .lam' α t

def TmQ.const (n : HOLean.Name) (ty : TyQ) : TmQ :=
  match ty with
  | .val ty => .val (.const n ty)
  | ty => .const' n ty

def TmQ.fvar (x : HOLean.Name) (α : TyQ) : TmQ :=
  match α with
  | .val α => .val (.fvar x α)
  | α => .fvar' x α

partial def TmQ.toTm? : TmQ → Option Tm
  | .val t => some t
  | .splice _ => none
  | .app' f a => do return Tm.app (← f.toTm?) (← a.toTm?)
  | .lam' (.val α) t => do return Tm.lam α (← t.toTm?)
  | .lam' _ _ => none
  | .fvar' x (.val α) => some (.fvar x α)
  | .fvar' _ _ => none
  | .const' n (.val α) => some (.const n α)
  | .const' _ _ => none

partial def TmQ.toExpr (t : TmQ) : Expr :=
  match t.toTm? with
  | some t => Lean.toExpr t
  | none =>
    match t with
    | .val t => Lean.toExpr t
    | .splice e => e
    | .app' f a => mkApp2 (mkConst ``Tm.app) f.toExpr a.toExpr
    | .lam' α t => mkApp2 (mkConst ``Tm.lam) α.toExpr t.toExpr
    | .fvar' x α => mkApp2 (mkConst ``Tm.fvar) (Lean.toExpr x) α.toExpr
    | .const' n α => mkApp2 (mkConst ``Tm.const) (Lean.toExpr n) α.toExpr

partial def TmQ.closeAt (t : TmQ) (k : Nat) (x : HOLean.Name) (α : TyQ) : TmQ :=
  match t with
  | .val t =>
    match α with
    | .val α => .val (t.closeAt k x α)
    | .expr _ => .val t
  | .splice e => .splice e
  | .app' f a => (f.closeAt k x α).app (a.closeAt k x α)
  | .lam' β t => TmQ.lam β (t.closeAt (k + 1) x α)
  | .fvar' y β => if y == x && β.beq α then .val (.bvar k) else .fvar' y β
  | .const' n τ => .const' n τ

def TmQ.abstract (t : TmQ) (x : HOLean.Name) (α : TyQ) : TmQ :=
  TmQ.lam α (t.closeAt 0 x α)

def TmQ.eqConst (α : TyQ) : TmQ :=
  match α with
  | .val α => .val (Tm.eqConst α)
  | α => TmQ.const eqName (α.arrow (α.arrow (.val .bool)))

def TmQ.mkEq (α : TyQ) (s t : TmQ) : TmQ :=
  (TmQ.eqConst α).app s |>.app t

def TmQ.not (t : TmQ) : TmQ :=
  match t with
  | .val t => .val (Tm.not t)
  | t => (TmQ.const notName (.val notTy)).app t

def TmQ.imp (p q : TmQ) : TmQ :=
  match p, q with
  | .val p, .val q => .val (Tm.imp p q)
  | p, q => (TmQ.const impName (.val impTy)).app p |>.app q

def TmQ.all (α : TyQ) (P : TmQ) : TmQ :=
  match α, P with
  | .val α, .val P => .val (Tm.all α P)
  | α, P => (TmQ.const allName ((α.arrow (.val .bool)).arrow (.val .bool))).app P

def TmQ.selectConst (α : TyQ) : TmQ :=
  TmQ.const selectName ((α.arrow (.val .bool)).arrow α)

def TmQ.oneOne (α β : TyQ) (f : TmQ) : TmQ :=
  (TmQ.const oneOneName (((α.arrow β).arrow (.val .bool)))).app f

def TmQ.onto (α β : TyQ) (f : TmQ) : TmQ :=
  (TmQ.const ontoName (((α.arrow β).arrow (.val .bool)))).app f

def TmQ.force (t : TmQ) : MetaM Tm :=
  match t.toTm? with
  | some t => return t
  | none => decodeTm t.toExpr

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
  return e.consumeMData

def throwIfMVar (e : Expr) : MetaM Unit := do
  if e.hasExprMVar then
    throwError "HOLean: expression still has metavariables{indentExpr e}"

mutual

/-- Apply a HOL head to Lean arguments, each translated as a term. -/
partial def apps (head : TmQ) (args : Array Expr) : MetaM TmQ :=
  args.foldlM (init := head) fun t a =>
    return t.app (← exprToTm a)

/-- Translate a Lean type (`e : Type u` or `e = Prop`) to a HOL type. -/
partial def exprToTy (e : Expr) : MetaM TyQ := do
  let e ← ready e
  if let some α := isHolTyQuote? e then
    throwIfMVar α
    return .expr α
  throwIfMVar e
  let e ← whnf e
  match e with
  | .sort l =>
    if l.isZero then
      return .val .bool
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
    return .val (.var (holName decl.userName))
  | .const n _ =>
    if n == `Prop || n == ``Bool then
      return .val .bool
    else if n == ``Nat || n == ``HOLean.Ind then
      return .val .ind
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
        return (← exprToTy α).arrow (← exprToTy body')
  | .letE _ _ v b _ =>
    exprToTy (b.instantiate1 v)
  | .mdata _ e =>
    exprToTy e
  | _ =>
    throwError "HOLean: not a simple type{indentExpr e}"

/-- Known Lean constants that denote HOL primitives or connectives. -/
partial def translateConst (n : Lean.Name) (args : Array Expr) : MetaM (Option TmQ) := do
  match n with
  | ``True | ``Bool.true =>
    if args.isEmpty then return some (.val Tm.tru) else return none
  | ``False | ``Bool.false =>
    if args.isEmpty then return some (.val Tm.falsum) else return none
  | ``And | ``Bool.and =>
    some <$> apps (.val (.const andName andTy)) args
  | ``Or | ``Bool.or =>
    some <$> apps (.val (.const orName orTy)) args
  | ``Not | ``Bool.not =>
    some <$> apps (.val (.const notName notTy)) args
  | ``Iff =>
    some <$> apps (TmQ.eqConst (.val .bool)) args
  | ``Eq =>
    if args.isEmpty then
      throwError "HOLean: `Eq` needs a type argument"
    else
      let α ← exprToTy args[0]!
      some <$> apps (TmQ.eqConst α) args[1:]
  | ``Ne =>
    match args with
    | #[α, x, y] =>
      return some ((TmQ.mkEq (← exprToTy α) (← exprToTm x) (← exprToTm y)).not)
    | _ => return none
  | ``Exists =>
    if args.isEmpty then
      throwError "HOLean: `Exists` needs a type argument"
    else
      let α ← exprToTy args[0]!
      some <$> apps (TmQ.const exName ((α.arrow (.val .bool)).arrow (.val .bool))) args[1:]
  | ``Classical.epsilon =>
    match args with
    | #[α, _inst, p] =>
      return some ((TmQ.selectConst (← exprToTy α)).app (← exprToTm p))
    | #[α, _inst] =>
      return some (TmQ.selectConst (← exprToTy α))
    | _ => return none
  | ``id =>
    match args with
    | #[α] =>
      let α ← exprToTy α
      return some (TmQ.lam α (.val (.bvar 0)))
    | #[_α, x] => some <$> exprToTm x
    | _ => return none
  | ``HOLean.oneOne =>
    match args with
    | #[α, β, f] =>
      return some (TmQ.oneOne (← exprToTy α) (← exprToTy β) (← exprToTm f))
    | #[α, β] =>
      let τ := ((← exprToTy α).arrow (← exprToTy β)).arrow (.val .bool)
      return some (TmQ.const oneOneName τ)
    | _ => return none
  | ``HOLean.onto =>
    match args with
    | #[α, β, f] =>
      return some (TmQ.onto (← exprToTy α) (← exprToTy β) (← exprToTm f))
    | #[α, β] =>
      let τ := ((← exprToTy α).arrow (← exprToTy β)).arrow (.val .bool)
      return some (TmQ.const ontoName τ)
    | _ => return none
  | n =>
    if let some (holName, gen) := findUserDef? (← getEnv) n then
      some <$> applyUserConst holName gen args
    else if args.isEmpty then
      if let some stmt := findUserThmByLean? (← getEnv) n then
        return some (.val stmt)
      else
        return none
    else
      return none

/-- Apply a user `hdef` constant, instantiating schematic type variables
from Lean type arguments and from the types of term arguments. -/
partial def applyUserConst (holName : HOLean.Name) (gen : Ty) (args : Array Expr) :
    MetaM TmQ := do
  let mut θ : TySubst := []
  let mut targs : Array Expr := #[]
  for a in args do
    let aTy ← whnf (← inferType a)
    if aTy.isSort && !aTy.isProp then
      let tvs := gen.tyvars.filter fun x => (θ.lookup x).isNone
      if tvs.isEmpty then
        throwError "HOLean: extra type argument{indentExpr a}"
      let τ ← (← exprToTy a).force
      θ := θ ++ [(tvs[0]!, τ)]
    else
      targs := targs.push a
  let mut rest := gen.inst θ
  for a in targs do
    match rest with
    | .arrow α β =>
      let aTy ← (← exprToTy (← inferType a)).force
      match α.matchTy aTy θ with
      | some θ' =>
        θ := θ'
        rest := β.inst θ
      | none =>
        throwError "HOLean: cannot instantiate `{holName}` at argument{indentExpr a}"
    | _ =>
      throwError "HOLean: too many arguments to `{holName}`"
  apps (TmQ.const holName (.val (gen.inst θ))) targs

/-- Translate a Lean term or proposition to a HOL term. -/
partial def exprToTm (e : Expr) : MetaM TmQ := do
  let e ← ready e
  if let some (t, extras) ← destTmSplice? e then
    throwIfMVar t
    let mut q : TmQ := .splice t
    for a in extras do
      -- `CoeFun` inserts implicit Lean type arguments; those are not HOL apps.
      let aTy ← whnf (← inferType a)
      unless aTy.isSort && !aTy.isProp do
        q := q.app (← exprToTm a)
    return q
  throwIfMVar e
  match e with
  | .mdata _ e =>
    exprToTm e
  | .fvar id =>
    let decl ← id.getDecl
    let ty ← whnf decl.type
    if ty.isSort && !ty.isProp then
      throwError "HOLean: type variable `{decl.userName}` is a HOL type, not a term"
    return TmQ.fvar (holName decl.userName) (← exprToTy decl.type)
  | .bvar i =>
    return .val (.bvar i)
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
          return (← exprToTm α).imp (← exprToTm body')
        else
          let αT ← exprToTy α
          let t ← exprToTm body'
          return TmQ.all αT (t.abstract (holName (← x.fvarId!.getUserName)) αT)
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
        t := t.app (← exprToTm a)
      return t
  | .mvar .. =>
    throwError "HOLean: unassigned metavariable{indentExpr e}"
  | .lit .. =>
    throwError "HOLean: literals are not HOL terms{indentExpr e}"
  | .proj .. =>
    throwError "HOLean: structure projections are not HOL terms{indentExpr e}"

end

/-- Translate a Lean type to a closed `Ty` (no open antiquotations). -/
def exprToTyVal (e : Expr) : MetaM Ty := do
  (← exprToTy e).force

/-- Translate a Lean term to a closed `Tm` (no open antiquotations). -/
def exprToTmVal (e : Expr) : MetaM Tm := do
  (← exprToTm e).force

end HOLean.Elab
