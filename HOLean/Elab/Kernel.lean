/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Elab.State
import HOLean.Elab.ProvTrace

/-!
# Executable LCF kernel

`Provable` is a metatheoretic predicate.  Commands need something we can
*run*: `Thm` is an LCF-style sequent, and `Hol.*` are the ten kernel
rules plus a few derived combinators, as Lean functions.

Each `Hol.*` returns a `CertifiedThm`: the sequent together with a
`ProvTrace` that `Replay.buildProvable` later turns into a kernel
`Provable` proof for certificates.

`htheorem` evaluates a `HolM CertifiedThm` script against the current
environment.
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

/-- A checked sequent plus the derivation used to obtain it. -/
structure CertifiedThm where
  thm : Thm
  trace : ProvTrace
  deriving Inhabited

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

/-- Look up the Lean name of a user `htheorem` for `ProvTrace.named`. -/
def HolCtx.thmLeanName? (ctx : HolCtx) (n : HOLean.Name) : Option Lean.Name :=
  ctx.decls.findSome? fun
    | .thm ln hn _ => if hn == n || ln.toString == n then some ln else none
    | .defn .. => none

namespace Hol

def infer (t : Tm) : HolM Ty := do
  match t.infer (← read).env [] with
  | some α => return α
  | none => HolM.throw s!"not well-typed: {repr t}"

def inferCtx (t : Tm) (Γ : List Ty) : HolM Ty := do
  match t.infer (← read).env Γ with
  | some α => return α
  | none => HolM.throw s!"not well-typed: {repr t}"

/-- Wrap a sequent and its derivation. -/
def mk (hyps : List Tm) (concl : Tm) (trace : ProvTrace) : CertifiedThm :=
  { thm := { hyps, concl }, trace }

/-- `REFL t` gives `⊢ t = t`. -/
def refl (t : Tm) : HolM CertifiedThm := do
  let α ← infer t
  return mk [] (Tm.mkEq α t t) (.refl t α)

/-- `TRANS`. -/
def trans (th1 th2 : CertifiedThm) : HolM CertifiedThm := do
  match Tm.destEq th1.thm.concl, Tm.destEq th2.thm.concl with
  | some (α, s, t), some (β, t', u) =>
    if α == β && t == t' then
      return mk (th1.thm.hyps ++ th2.thm.hyps) (Tm.mkEq α s u)
        (.trans th1.trace th2.trace)
    else
      HolM.throw "TRANS: conclusions do not join"
  | _, _ => HolM.throw "TRANS: expected equations"

/-- `MK_COMB`. -/
def mkComb (th1 th2 : CertifiedThm) : HolM CertifiedThm := do
  match Tm.destEq th1.thm.concl, Tm.destEq th2.thm.concl with
  | some (.arrow α β, f, g), some (α', x, y) =>
    if α == α' then
      return mk (th1.thm.hyps ++ th2.thm.hyps)
        (Tm.mkEq β (.app f x) (.app g y))
        (.mkComb th1.trace th2.trace)
    else
      HolM.throw "MK_COMB: domain mismatch"
  | _, _ => HolM.throw "MK_COMB: expected an equation of function type and an argument equation"

/-- `ABS`: close the free variable `(x, α)` on both sides. -/
def abs (x : HOLean.Name) (α : Ty) (th : CertifiedThm) : HolM CertifiedThm := do
  if th.thm.hyps.any (fun p => p.freeIn x α) then
    HolM.throw s!"ABS: variable {x} is free in the hypotheses"
  match Tm.destEq th.thm.concl with
  | some (β, s, t) =>
    return mk th.thm.hyps
      (Tm.mkEq (α ↝ β) (s.abstract x α) (t.abstract x α))
      (.abs x α th.trace)
  | none => HolM.throw "ABS: expected an equation"

/-- `BETA`: `⊢ ((λ x. t) x) = t[x]`. -/
def beta (x : HOLean.Name) (α : Ty) (t : Tm) : HolM CertifiedThm := do
  let β ← inferCtx t [α]
  return mk []
    (Tm.mkEq β (.app (.lam α t) (.fvar x α)) (t.open' (.fvar x α)))
    (.beta t x α)

/-- `ASSUME p` gives `{p} ⊢ p`. -/
def assume (p : Tm) : HolM CertifiedThm := do
  let α ← infer p
  unless α == .bool do
    HolM.throw "ASSUME: expected a boolean"
  return mk [p] p (.assume p)

/-- `EQ_MP`. -/
def eqMp (th1 th2 : CertifiedThm) : HolM CertifiedThm := do
  match Tm.destEq th1.thm.concl with
  | some (.bool, p, q) =>
    if p == th2.thm.concl then
      return mk (th1.thm.hyps ++ th2.thm.hyps) q (.eqMp th1.trace th2.trace)
    else
      HolM.throw "EQ_MP: left-hand side does not match the second theorem"
  | _ => HolM.throw "EQ_MP: expected a boolean equation"

/-- `DEDUCT_ANTISYM_RULE`. -/
def deductAntisym (th1 th2 : CertifiedThm) : HolM CertifiedThm :=
  return mk
    (hypsErase th2.thm.concl th1.thm.hyps ++ hypsErase th1.thm.concl th2.thm.hyps)
    (Tm.mkEq .bool th1.thm.concl th2.thm.concl)
    (.deductAntisym th1.trace th2.trace)

/-- `INST_TYPE`. -/
def instType (θ : TySubst) (th : CertifiedThm) : HolM CertifiedThm :=
  return mk
    (th.thm.hyps.map (·.instTy θ))
    (th.thm.concl.instTy θ)
    (.instType θ th.trace)

/-- `INST` (type-preserving substitution of free variables). -/
def inst (σ : Tm.Subst) (th : CertifiedThm) : HolM CertifiedThm := do
  let env := (← read).env
  for p in σ do
    let α := p.2.1
    let u := p.2.2
    match u.infer env [] with
    | some α' =>
      unless α == α' do
        HolM.throw s!"INST: replacement has type {repr α'}, expected {repr α}"
    | none => HolM.throw s!"INST: replacement is not well-typed: {repr u}"
  return mk
    (th.thm.hyps.map (·.applySubst σ))
    (th.thm.concl.applySubst σ)
    (.inst σ th.trace)

/-- Defining equation `⊢ c = rhs` of a constant (built-in or `hdef`). -/
def defn (n : HOLean.Name) : HolM CertifiedThm := do
  match (← read).defOf n with
  | some (ty, rhs) =>
    let p := Tm.mkEq ty (.const n ty) rhs
    return mk [] p (.ax p)
  | none => HolM.throw s!"no definition for `{n}`"

/-- A previously installed `htheorem`. -/
def thm (n : HOLean.Name) : HolM CertifiedThm := do
  let ctx ← read
  match findUserThm? ctx.decls n with
  | some stmt =>
    match ctx.thmLeanName? n with
    | some leanN => return mk [] stmt (.named leanN)
    | none => HolM.throw s!"no Lean name for theorem `{n}`"
  | none => HolM.throw s!"no theorem `{n}`"

/-- `SPEC`: from `Γ ⊢ ∀ (λ x. body)` conclude `Γ ⊢ body[t]`. -/
def spec (t : Tm) (th : CertifiedThm) : HolM CertifiedThm := do
  match th.thm.concl with
  | .app (.const n ((.arrow α .bool) ↝ .bool)) (.lam β body) =>
    unless n == allName do
      HolM.throw "SPEC: expected a universal quantifier"
    unless β == α do
      HolM.throw s!"SPEC: binder type {repr β} ≠ domain {repr α}"
    let τt ← infer t
    unless τt == α do
      HolM.throw s!"SPEC: term has type {repr τt}, expected {repr α}"
    return mk th.thm.hyps (body.open' t) (.spec t α th.trace)
  | .app (.const n ((.arrow α .bool) ↝ .bool)) P =>
    unless n == allName do
      HolM.throw "SPEC: expected a universal quantifier"
    let τt ← infer t
    unless τt == α do
      HolM.throw s!"SPEC: term has type {repr τt}, expected {repr α}"
    return mk th.thm.hyps (P.app t) (.spec t α th.trace)
  | _ => HolM.throw "SPEC: expected `∀ P`"

/-- One η instance: `⊢ (λ x. f x) = f`, from the closed ETA axiom via
`INST_TYPE` and `SPEC`. -/
def eta (α β : Ty) (f : Tm) : HolM CertifiedThm := do
  let τ ← infer f
  unless τ == α ↝ β do
    HolM.throw s!"ETA: expected type {repr (α ↝ β)}, got {repr τ}"
  let th0 := mk [] etaAxiom (.ax etaAxiom)
  let θ : TySubst := [(primTyVar, α), (primTyVarB, β)]
  let th1 ← instType θ th0
  Hol.spec f th1

/-- One SELECT instance: `⊢ P x ⇒ P (ε P)`, from the closed SELECT axiom. -/
def select (α : Ty) (P x : Tm) : HolM CertifiedThm := do
  let τP ← infer P
  let τx ← infer x
  unless τP == α ↝ .bool do
    HolM.throw s!"SELECT: predicate has type {repr τP}"
  unless τx == α do
    HolM.throw s!"SELECT: witness has type {repr τx}"
  let th0 := mk [] selectAxiom (.ax selectAxiom)
  let θ : TySubst := [(primTyVar, α)]
  let th1 ← instType θ th0
  let th2 ← Hol.spec P th1
  Hol.spec x th2

/-- The infinity axiom. -/
def infinity : HolM CertifiedThm :=
  return mk [] infinityAxiom (.ax infinityAxiom)

/-- `Γ ⊢ s = t` implies `Γ ⊢ t = s`. -/
def sym (th : CertifiedThm) : HolM CertifiedThm := do
  match Tm.destEq th.thm.concl with
  | some (α, s, t) =>
    return mk th.thm.hyps (Tm.mkEq α t s) (.eqSym th.trace)
  | none => HolM.throw "SYM: expected an equation"

/-- `⊢ T`. -/
def truth : HolM CertifiedThm :=
  return mk [] Tm.tru .truth

/-- Discharge: from `Γ ⊢ q` conclude `Γ \ {p} ⊢ p ⇒ q`.

This is the standard HOL `DISCH`.  The executable kernel applies it as a
sequent update; `Provable` replay of `DISCH` is not yet implemented. -/
def disch (p : Tm) (th : CertifiedThm) : HolM CertifiedThm := do
  let α ← infer p
  unless α == .bool do
    HolM.throw "DISCH: expected a boolean antecedent"
  unless p.LC 0 do
    HolM.throw "DISCH: antecedent is not locally closed"
  return mk (th.thm.hyps.filter (· != p)) (Tm.imp p th.thm.concl)
    (.disch p th.trace)

/-- Generalize: from `Γ ⊢ t` with `x` not free in `Γ`, conclude
`Γ ⊢ ∀ x. t`.  Matches `Provable.gen`. -/
def gen (x : HOLean.Name) (α : Ty) (th : CertifiedThm) : HolM CertifiedThm := do
  if th.thm.hyps.any (fun p => p.freeIn x α) then
    HolM.throw s!"GEN: variable {x} is free in the hypotheses"
  if th.thm.hyps.contains Tm.tru then
    HolM.throw "GEN: T is a hypothesis"
  let τ ← infer th.thm.concl
  unless τ == .bool do
    HolM.throw "GEN: expected a boolean conclusion"
  return mk th.thm.hyps (Tm.all α (th.thm.concl.abstract x α))
    (.gen x α th.trace)

end Hol

end Elab
end HOLean
