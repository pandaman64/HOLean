/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Elab.State

/-!
# Executable LCF kernel

`Provable` is a metatheoretic predicate.  Commands need something we can
*run*: `Thm` is an LCF-style sequent, and `Hol.*` are the ten kernel
rules plus a few derived combinators, as Lean functions.

`htheorem` evaluates a `HolM Thm` script against the current environment.
A full tactic language can replace this later; the scripts are ordinary
Lean terms for now.
-/

namespace HOLean
namespace Elab

/-- A checked HOL sequent `hyps ⊢ concl`.  Only `Hol.*` should construct
these; `htheorem` re-checks `hyps = []` and the expected conclusion. -/
structure Thm where
  hyps : List Tm
  concl : Tm
  deriving Repr, BEq, Inhabited

deriving instance Lean.ToExpr for Thm

/-- Context for a proof script: the current HOL environment and the user
declarations used to recognise definitions / previous theorems. -/
structure HolCtx where
  env : Env
  decls : HolState

abbrev HolM := ReaderT HolCtx (Except String)

def HolM.run (x : HolM α) (ctx : HolCtx) : Except String α :=
  ReaderT.run x ctx

def HolM.throw (msg : String) : HolM α :=
  fun _ => .error msg

/-- Defining right-hand side of a built-in `addDef` constant. -/
def builtinDef? (n : HOLean.Name) : Option (Ty × Tm) :=
  if n == truName then some (truTy, Tm.truDef)
  else if n == andName then some (andTy, Tm.andDef)
  else if n == impName then some (impTy, Tm.impDef)
  else if n == allName then some (allTy, Tm.allDef)
  else if n == falsumName then some (falsumTy, Tm.falsumDef)
  else if n == notName then some (notTy, Tm.notDef)
  else if n == orName then some (orTy, Tm.orDef)
  else if n == exName then some (exTy, Tm.exDef)
  else if n == oneOneName then some (oneOneTy, Tm.oneOneDef)
  else if n == ontoName then some (ontoTy, Tm.ontoDef)
  else none

def HolCtx.defOf (ctx : HolCtx) (n : HOLean.Name) : Option (Ty × Tm) :=
  match findUserDefByHol? ctx.decls n with
  | some p => some p
  | none => builtinDef? n

namespace Hol

def infer (t : Tm) : HolM Ty := do
  match t.infer (← read).env [] with
  | some α => return α
  | none => HolM.throw s!"not well-typed: {repr t}"

def inferCtx (t : Tm) (Γ : List Ty) : HolM Ty := do
  match t.infer (← read).env Γ with
  | some α => return α
  | none => HolM.throw s!"not well-typed: {repr t}"

/-- `REFL t` gives `⊢ t = t`. -/
def refl (t : Tm) : HolM Thm := do
  let α ← infer t
  return { hyps := [], concl := Tm.mkEq α t t }

/-- `TRANS`. -/
def trans (th1 th2 : Thm) : HolM Thm := do
  match Tm.destEq th1.concl, Tm.destEq th2.concl with
  | some (α, s, t), some (β, t', u) =>
    if α == β && t == t' then
      return { hyps := th1.hyps ++ th2.hyps, concl := Tm.mkEq α s u }
    else
      HolM.throw "TRANS: conclusions do not join"
  | _, _ => HolM.throw "TRANS: expected equations"

/-- `MK_COMB`. -/
def mkComb (th1 th2 : Thm) : HolM Thm := do
  match Tm.destEq th1.concl, Tm.destEq th2.concl with
  | some (.arrow α β, f, g), some (α', x, y) =>
    if α == α' then
      return { hyps := th1.hyps ++ th2.hyps, concl := Tm.mkEq β (.app f x) (.app g y) }
    else
      HolM.throw "MK_COMB: domain mismatch"
  | _, _ => HolM.throw "MK_COMB: expected an equation of function type and an argument equation"

/-- `ABS`: close the free variable `(x, α)` on both sides. -/
def abs (x : HOLean.Name) (α : Ty) (th : Thm) : HolM Thm := do
  if th.hyps.any (fun p => p.freeIn x α) then
    HolM.throw s!"ABS: variable {x} is free in the hypotheses"
  match Tm.destEq th.concl with
  | some (β, s, t) =>
    return {
      hyps := th.hyps
      concl := Tm.mkEq (α ↝ β) (s.abstract x α) (t.abstract x α)
    }
  | none => HolM.throw "ABS: expected an equation"

/-- `BETA`: `⊢ ((λ x. t) x) = t[x]`. -/
def beta (x : HOLean.Name) (α : Ty) (t : Tm) : HolM Thm := do
  let β ← inferCtx t [α]
  return {
    hyps := []
    concl := Tm.mkEq β (.app (.lam α t) (.fvar x α)) (t.open' (.fvar x α))
  }

/-- `ASSUME p` gives `{p} ⊢ p`. -/
def assume (p : Tm) : HolM Thm := do
  let α ← infer p
  unless α == .bool do
    HolM.throw "ASSUME: expected a boolean"
  return { hyps := [p], concl := p }

/-- `EQ_MP`. -/
def eqMp (th1 th2 : Thm) : HolM Thm := do
  match Tm.destEq th1.concl with
  | some (.bool, p, q) =>
    if p == th2.concl then
      return { hyps := th1.hyps ++ th2.hyps, concl := q }
    else
      HolM.throw "EQ_MP: left-hand side does not match the second theorem"
  | _ => HolM.throw "EQ_MP: expected a boolean equation"

/-- `DEDUCT_ANTISYM_RULE`. -/
def deductAntisym (th1 th2 : Thm) : HolM Thm :=
  return {
    hyps := hypsErase th2.concl th1.hyps ++ hypsErase th1.concl th2.hyps
    concl := Tm.mkEq .bool th1.concl th2.concl
  }

/-- `INST_TYPE`. -/
def instType (θ : TySubst) (th : Thm) : HolM Thm :=
  return {
    hyps := th.hyps.map (·.instTy θ)
    concl := th.concl.instTy θ
  }

/-- `INST` (type-preserving substitution of free variables). -/
def inst (σ : Tm.Subst) (th : Thm) : HolM Thm := do
  let env := (← read).env
  for p in σ do
    let α := p.2.1
    let u := p.2.2
    match u.infer env [] with
    | some α' =>
      unless α == α' do
        HolM.throw s!"INST: replacement has type {repr α'}, expected {repr α}"
    | none => HolM.throw s!"INST: replacement is not well-typed: {repr u}"
  return {
    hyps := th.hyps.map (·.applySubst σ)
    concl := th.concl.applySubst σ
  }

/-- Defining equation `⊢ c = rhs` of a constant (built-in or `hdef`). -/
def defn (n : HOLean.Name) : HolM Thm := do
  match (← read).defOf n with
  | some (ty, rhs) =>
    return { hyps := [], concl := Tm.mkEq ty (.const n ty) rhs }
  | none => HolM.throw s!"no definition for `{n}`"

/-- A previously installed `htheorem`. -/
def thm (n : HOLean.Name) : HolM Thm := do
  match findUserThm? (← read).decls n with
  | some stmt =>
    return { hyps := [], concl := stmt }
  | none => HolM.throw s!"no theorem `{n}`"

/-- One η instance: `⊢ (λ x. f x) = f`. -/
def eta (α β : Ty) (f : Tm) : HolM Thm := do
  let τ ← infer f
  unless τ == α ↝ β do
    HolM.throw s!"ETA: expected type {repr (α ↝ β)}, got {repr τ}"
  return { hyps := [], concl := etaAxiom α β f }

/-- One SELECT instance: `⊢ P x ⇒ P (ε P)`. -/
def select (α : Ty) (P x : Tm) : HolM Thm := do
  let τP ← infer P
  let τx ← infer x
  unless τP == α ↝ .bool do
    HolM.throw s!"SELECT: predicate has type {repr τP}"
  unless τx == α do
    HolM.throw s!"SELECT: witness has type {repr τx}"
  return { hyps := [], concl := selectAxiom α P x }

/-- The infinity axiom. -/
def infinity : HolM Thm :=
  return { hyps := [], concl := infinityAxiom }

/-- `Γ ⊢ s = t` implies `Γ ⊢ t = s`. -/
def sym (th : Thm) : HolM Thm := do
  match Tm.destEq th.concl with
  | some (α, s, _) =>
    let req ← refl (Tm.eqConst α)
    let hfun ← mkComb req th
    let rs ← refl s
    let hbool ← mkComb hfun rs
    eqMp hbool rs
  | none => HolM.throw "SYM: expected an equation"

/-- `⊢ T`. -/
def truth : HolM Thm := do
  let d ← defn truName
  let s ← sym d
  let r ← refl (.lam .bool (.bvar 0))
  eqMp s r

/-- Discharge: from `Γ ⊢ q` conclude `Γ \ {p} ⊢ p ⇒ q`.

This is the standard HOL `DISCH`.  The executable kernel applies it as a
sequent update; `Provable` replay of `DISCH` is not yet implemented. -/
def disch (p : Tm) (th : Thm) : HolM Thm := do
  let α ← infer p
  unless α == .bool do
    HolM.throw "DISCH: expected a boolean antecedent"
  unless p.LC 0 do
    HolM.throw "DISCH: antecedent is not locally closed"
  return { hyps := th.hyps.filter (· != p), concl := Tm.imp p th.concl }

/-- Generalize: from `Γ ⊢ t` with `x` not free in `Γ`, conclude
`Γ ⊢ ∀ x. t`.  Matches `Provable.gen`. -/
def gen (x : HOLean.Name) (α : Ty) (th : Thm) : HolM Thm := do
  if th.hyps.any (fun p => p.freeIn x α) then
    HolM.throw s!"GEN: variable {x} is free in the hypotheses"
  if th.hyps.contains Tm.tru then
    HolM.throw "GEN: T is a hypothesis"
  let τ ← infer th.concl
  unless τ == .bool do
    HolM.throw "GEN: expected a boolean conclusion"
  return { hyps := th.hyps, concl := Tm.all α (th.concl.abstract x α) }

end Hol

end Elab
end HOLean
