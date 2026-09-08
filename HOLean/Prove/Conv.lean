/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Prove.Kernel

/-!
# Derived equality combinators, as `ProveM` programs

SYM, AP_TERM, general β, `⊢ T`, and `EQT_INTRO` / `EQT_ELIM` are assembled
from the ten kernel primitives plus `defn`.  They do not call the Lean
metatheorems in `HOLean.Derived`.
-/

namespace HOLean
namespace Prove
namespace Hol

variable {env : Env}

/-- Unpack `Γ ⊢ s = t`. -/
def destEqCert (th : CertifiedThm env) : ProveM env (Ty × Tm × Tm) :=
  match Tm.destEq th.concl with
  | some trip => return trip
  | none => ProveM.throw "expected an equation"

/-- `AP_TERM f`: from `Γ ⊢ s = t` conclude `Γ ⊢ f s = f t`. -/
def apTerm (f : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  mkComb (← refl f) th

/-- `AP_THM`: from `Γ ⊢ f = g` conclude `Γ ⊢ f x = g x`. -/
def apThm (th : CertifiedThm env) (x : Tm) : ProveM env (CertifiedThm env) := do
  mkComb th (← refl x)

/-- `SYM`, following HOL Light: `EQ_MP (MK_COMB (AP_TERM (=) th) (REFL s)) (REFL s)`. -/
def sym (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match Tm.destEq th.concl with
  | some (α, s, _) =>
    let hs ← refl s
    eqMp (← mkComb (← apTerm (Tm.eqConst α) th) hs) hs
  | none => ProveM.throw "SYM: expected an equation"

/-- Combinator name used to instantiate primitive `BETA`. -/
def freshBetaName : Name := "_beta"

/-- General β: `⊢ (λ x. t) u = t[u]`, by `BETA` then `INST`. -/
def betaApp (f u : Tm) : ProveM env (CertifiedThm env) :=
  match f with
  | .lam α t => do
    let x := freshBetaName
    if t.freeIn x α then
      ProveM.throw s!"BETA: `{x}` is free in the body"
    inst [(x, α, u)] (← beta x α t)
  | _ =>
    ProveM.throw "BETA: expected a lambda"

/-- β-reduce the left-hand side of an equation. -/
def landBeta (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match Tm.destEq th.concl with
  | some (_, .app f u, _) =>
    trans (← sym (← betaApp f u)) th
  | some _ => ProveM.throw "LAND_BETA: lhs is not a redex"
  | none => ProveM.throw "LAND_BETA: expected an equation"

/-- β-reduce the right-hand side of an equation. -/
def randBeta (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match Tm.destEq th.concl with
  | some (_, _, .app f u) =>
    trans th (← betaApp f u)
  | some _ => ProveM.throw "RAND_BETA: rhs is not a redex"
  | none => ProveM.throw "RAND_BETA: expected an equation"

/-- β-reduce the rator of a binary application on the lhs: `(λx. t) v a`. -/
def ratorLandBeta (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match Tm.destEq th.concl with
  | some (_, .app (.app f v) a, _) =>
    let hβ ← betaApp f v
    trans (← sym (← apThm hβ a)) th
  | some _ => ProveM.throw "RATOR_LAND_BETA: lhs is not a nested redex"
  | none => ProveM.throw "RATOR_LAND_BETA: expected an equation"

/-- β-reduce the rator of a binary application on the rhs. -/
def ratorRandBeta (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match Tm.destEq th.concl with
  | some (_, _, .app (.app f v) a) =>
    let hβ ← betaApp f v
    trans th (← apThm hβ a)
  | some _ => ProveM.throw "RATOR_RAND_BETA: rhs is not a nested redex"
  | none => ProveM.throw "RATOR_RAND_BETA: expected an equation"

def isRedex : Tm → Bool
  | .app (.lam _ _) _ => true
  | _ => false

def isNestedRedex : Tm → Bool
  | .app (.app (.lam _ _) _) _ => true
  | _ => false

/-- Reduce β-redexes on either side of an equation, including `(λx. t) v a`. -/
def reduceBeta : Nat → CertifiedThm env → ProveM env (CertifiedThm env)
  | 0, th => return th
  | n + 1, th => do
    match Tm.destEq th.concl with
    | some (_, lhs, rhs) =>
      if isRedex lhs then
        reduceBeta n (← landBeta th)
      else if isRedex rhs then
        reduceBeta n (← randBeta th)
      else if isNestedRedex lhs then
        reduceBeta n (← ratorLandBeta th)
      else if isNestedRedex rhs then
        reduceBeta n (← ratorRandBeta th)
      else
        return th
    | none =>
      return th

/-- `⊢ T`, by unfolding the definition of `tru`. -/
def truth : ProveM env (CertifiedThm env) := do
  match Tm.destEq Tm.truDef with
  | some (_, l, _) =>
    eqMp (← sym (← defn truName)) (← refl l)
  | none =>
    ProveM.throw "TRUTH: `truDef` is not an equation"

/-- `EQT_INTRO`: from `Γ ⊢ p` conclude `Γ \ {T} ⊢ p = T`. -/
def eqtIntro (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  deductAntisym th (← truth)

/-- `EQT_ELIM`: from `Γ ⊢ p = T` conclude `Γ ⊢ p`. -/
def eqtElim (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  eqMp (← sym th) (← truth)

/-- Combinator name used to open a λ while proving a β-equality. -/
def freshConvName : Name := "_conv"

/-- Prove `⊢ s = t` when `s` and `t` are β-convertible (fuel-bounded). -/
def convBetaEq : Nat → Tm → Tm → ProveM env (CertifiedThm env)
  | 0, _, _ =>
    ProveM.throw "CONV: fuel exhausted"
  | n + 1, s, t =>
    if s == t then
      refl s
    else
      match s, t with
      | .app (.lam α b) u, _ => do
        let hβ ← betaApp (.lam α b) u
        let (_, _, s') ← destEqCert hβ
        trans hβ (← convBetaEq n s' t)
      | _, .app (.lam α b) u => do
        let hβ ← betaApp (.lam α b) u
        let (_, _, t') ← destEqCert hβ
        trans (← convBetaEq n s t') (← sym hβ)
      | .app f x, .app g y => do
        mkComb (← convBetaEq n f g) (← convBetaEq n x y)
      | .lam α s, .lam β t => do
        if α != β then
          ProveM.throw "CONV: lambda types differ"
        else do
          let x := freshConvName
          if s.freeIn x α || t.freeIn x α then
            ProveM.throw "CONV: combinator variable `_conv` is free"
          abs x α (← convBetaEq n (s.open' (.fvar x α)) (t.open' (.fvar x α)))
      | _, _ =>
        ProveM.throw "CONV: not β-convertible"

/-- Rewrite `Γ ⊢ p` to `Γ ⊢ q` when `p` and `q` are β-convertible. -/
def convConcl (q : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  if th.concl == q then
    return th
  else
    eqMp (← convBetaEq 32 th.concl q) th

end Hol
end Prove
end HOLean
