/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Prove.Conv

/-!
# Connective intro/elim as `ProveM` programs

Harrison / Andrews connectives are unfolded with `defn` + `MK_COMB` + `BETA`,
then the usual LCF rules (CONJ, MP, GEN, SPEC, …) are built from kernel
primitives.  None of this calls `HOLean.Derived`.
-/

namespace HOLean
namespace Prove
namespace Hol

variable {env : Env}

/-! ## Destructors -/

def destBin (n : Name) : Tm → Option (Tm × Tm)
  | .app (.app (.const c _) p) q => if c == n then some (p, q) else none
  | _ => none

def destUn (n : Name) : Tm → Option Tm
  | .app (.const c _) p => if c == n then some p else none
  | _ => none

def destAnd (t : Tm) : Option (Tm × Tm) := destBin andName t
def destImp (t : Tm) : Option (Tm × Tm) := destBin impName t
def destOr (t : Tm) : Option (Tm × Tm) := destBin orName t
def destNot (t : Tm) : Option Tm := destUn notName t

def destAll : Tm → Option (Ty × Tm)
  | .app (.const n ((.arrow α .bool) ↝ .bool)) P =>
    if n == allName then some (α, P) else none
  | _ => none

def destEx : Tm → Option (Ty × Tm)
  | .app (.const n ((.arrow α .bool) ↝ .bool)) P =>
    if n == exName then some (α, P) else none
  | _ => none

/-! ## Unfolding definitions -/

/-- `⊢ c p q = rhs[p, q]` for a binary defined constant. -/
def unfoldBin (n : Name) (p q : Tm) : ProveM env (CertifiedThm env) := do
  let hd ← defn n
  let (_, _, rhs) ← destEqCert hd
  let hβ1 ← betaApp rhs p
  let h1 ← trans (← apThm hd p) hβ1
  let (_, _, rhs1) ← destEqCert hβ1
  trans (← apThm h1 q) (← betaApp rhs1 q)

def unfoldAnd (p q : Tm) : ProveM env (CertifiedThm env) :=
  unfoldBin andName p q

def unfoldImp (p q : Tm) : ProveM env (CertifiedThm env) :=
  unfoldBin impName p q

def unfoldOr (p q : Tm) : ProveM env (CertifiedThm env) :=
  unfoldBin orName p q

/-- `⊢ ¬p = (p ⇒ ⊥)`. -/
def unfoldNot (p : Tm) : ProveM env (CertifiedThm env) := do
  let hd ← defn notName
  let (_, _, rhs) ← destEqCert hd
  trans (← apThm hd p) (← betaApp rhs p)

/-- `⊢ ⊥ = ∀ (λ p. p)`. -/
def unfoldFalsum : ProveM env (CertifiedThm env) :=
  defn falsumName

/-- `⊢ ∀ P = (P = λ x. T)` at type `α`. -/
def unfoldAll (α : Ty) (P : Tm) : ProveM env (CertifiedThm env) := do
  let hd ← instType [(primTyVar, α)] (← defn allName)
  let (_, _, rhs) ← destEqCert hd
  trans (← apThm hd P) (← betaApp rhs P)

/-- `⊢ ∃ P = ∀ q. (∀ x. P x ⇒ q) ⇒ q` at type `α`. -/
def unfoldEx (α : Ty) (P : Tm) : ProveM env (CertifiedThm env) := do
  let hd ← instType [(primTyVar, α)] (← defn exName)
  let (_, _, rhs) ← destEqCert hd
  trans (← apThm hd P) (← betaApp rhs P)

/-! ## Conjunction -/

def freshConjName : Name := "_conj"

/-- Boolean pair projections used to eliminate `∧`. -/
def projFst : Tm :=
  Tm.lam .bool (Tm.lam .bool (.bvar 1))

def projSnd : Tm :=
  Tm.lam .bool (Tm.lam .bool (.bvar 0))

/-- `CONJ`: from `Γ ⊢ p` and `Δ ⊢ q` conclude `Γ,Δ ⊢ p ∧ q`. -/
def conj (thp thq : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let p := thp.concl
  let q := thq.concl
  let x := freshConjName
  if p.freeIn x Tm.boolCombTy || q.freeIn x Tm.boolCombTy then
    ProveM.throw "CONJ: combinator variable `_conj` is free"
  let hpT ← eqtIntro thp
  let hqT ← eqtIntro thq
  let h2 ← mkComb (← mkComb (← refl (Tm.fvar x Tm.boolCombTy)) hpT) hqT
  let habs ← abs x Tm.boolCombTy h2
  eqMp (← sym (← unfoldAnd p q)) habs

/-- Apply a combinator to both sides of an unfolded conjunction and β-reduce. -/
def conjunctProj (π : Tm) (th : CertifiedThm env) :
    ProveM env (CertifiedThm env) := do
  match destAnd th.concl with
  | none => ProveM.throw "CONJUNCT: expected a conjunction"
  | some (p, q) =>
    let hexp ← eqMp (← unfoldAnd p q) th
    eqtElim (← reduceBeta 8 (← mkComb hexp (← refl π)))

/-- `CONJUNCT1`: `Γ ⊢ p ∧ q` implies `Γ ⊢ p`. -/
def conjunct1 (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  conjunctProj projFst th

/-- `CONJUNCT2`: `Γ ⊢ p ∧ q` implies `Γ ⊢ q`. -/
def conjunct2 (th : CertifiedThm env) : ProveM env (CertifiedThm env) :=
  conjunctProj projSnd th

/-! ## Implication -/

/-- `MP`: from `Γ ⊢ p ⇒ q` and `Δ ⊢ p` conclude `Γ,Δ ⊢ q`. -/
def mp (thimp thp : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match destImp thimp.concl with
  | none => ProveM.throw "MP: expected an implication"
  | some (p, q) =>
    if p != thp.concl then
      ProveM.throw "MP: antecedent does not match"
    else do
      let heq ← eqMp (← unfoldImp p q) thimp
      conjunct2 (← eqMp (← sym heq) thp)

/-- `DISCH p`: from `Γ ⊢ q` conclude `Γ \ {p} ⊢ p ⇒ q`. -/
def disch (p : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let q := th.concl
  let th1 ← conj (← assume p) th
  let th2 ← conjunct1 (← assume th1.concl)
  let th3 ← deductAntisym th1 th2
  eqMp (← sym (← unfoldImp p q)) th3

/-- Add an unused assumption `a` (CONJ + CONJUNCT2). -/
def addAssum (a : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  conjunct2 (← conj (← assume a) th)

/-! ## Quantifiers -/

/-- `GEN`: from `Γ ⊢ t` with `x` not free in `Γ`, conclude `Γ ⊢ ∀ x. t`. -/
def gen (x : Name) (α : Ty) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let habs ← abs x α (← eqtIntro th)
  eqMp (← sym (← unfoldAll α (th.concl.abstract x α))) habs

/-- `SPEC t`: from `Γ ⊢ ∀ P` conclude `Γ ⊢ P t` (and β if `P` is a λ). -/
def spec (t : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match destAll th.concl with
  | none => ProveM.throw "SPEC: expected a universal quantifier"
  | some (α, P) =>
    let hexp ← eqMp (← unfoldAll α P) th
    let ht ← eqtElim (← trans (← mkComb hexp (← refl t)) (← betaApp (.lam α Tm.tru) t))
    match P with
    | .lam β _ =>
      if β == α then
        eqMp (← betaApp P t) ht
      else
        ProveM.throw s!"SPEC: binder type {repr β} ≠ domain {repr α}"
    | _ =>
      return ht

/-! ## Falsity and negation -/

/-- `⊥`-elim: from `Γ ⊢ ⊥` conclude `Γ ⊢ q`. -/
def falsumElim (q : Tm) (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  unless th.concl == Tm.falsum do
    ProveM.throw "FALSUM_ELIM: expected `⊥`"
  spec q (← eqMp (← unfoldFalsum) th)

/-- From `Γ ⊢ p ⇒ ⊥` conclude `Γ ⊢ ¬ p`. -/
def notIntro (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match destImp th.concl with
  | some (p, f) =>
    unless f == Tm.falsum do
      ProveM.throw "NOT_INTRO: expected `p ⇒ ⊥`"
    eqMp (← sym (← unfoldNot p)) th
  | none =>
    ProveM.throw "NOT_INTRO: expected an implication"

/-- From `Γ ⊢ ¬ p` conclude `Γ ⊢ p ⇒ ⊥`. -/
def notElim (th : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match destNot th.concl with
  | some p =>
    eqMp (← unfoldNot p) th
  | none =>
    ProveM.throw "NOT_ELIM: expected a negation"

/-! ## Disjunction -/

def freshOrName : Name := "_or_r"

/-- `DISJ1`: from `Γ ⊢ p` conclude `Γ ⊢ p ∨ q`. -/
def disj1 (q : Tm) (thp : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let p := thp.concl
  let r := Tm.fvar freshOrName .bool
  if p.freeIn freshOrName .bool || q.freeIn freshOrName .bool then
    ProveM.throw "DISJ1: combinator variable `_or_r` is free"
  let th1 ← mp (← assume (Tm.imp p r)) thp
  let th2 ← addAssum (Tm.imp q r) th1
  let th3 ← disch (Tm.imp q r) th2
  let th4 ← disch (Tm.imp p r) th3
  eqMp (← sym (← unfoldOr p q)) (← gen freshOrName .bool th4)

/-- `DISJ2`: from `Γ ⊢ q` conclude `Γ ⊢ p ∨ q`. -/
def disj2 (p : Tm) (thq : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  let q := thq.concl
  let r := Tm.fvar freshOrName .bool
  if p.freeIn freshOrName .bool || q.freeIn freshOrName .bool then
    ProveM.throw "DISJ2: combinator variable `_or_r` is free"
  let th1 ← mp (← assume (Tm.imp q r)) thq
  let th2 ← addAssum (Tm.imp p r) th1
  let th3 ← disch (Tm.imp q r) th2
  let th4 ← disch (Tm.imp p r) th3
  eqMp (← sym (← unfoldOr p q)) (← gen freshOrName .bool th4)

/-- `DISJ_CASES`: from `Γ ⊢ p ∨ q`, `Δ ⊢ p ⇒ r`, `Θ ⊢ q ⇒ r` conclude `Γ,Δ,Θ ⊢ r`. -/
def disjElim (thor thpr thqr : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match destOr thor.concl, destImp thpr.concl, destImp thqr.concl with
  | some (p, q), some (p', r), some (q', r') =>
    unless p == p' && q == q' && r == r' do
      ProveM.throw "DISJ_CASES: operands do not match"
    let hall ← eqMp (← unfoldOr p q) thor
    mp (← mp (← spec r hall) thpr) thqr
  | _, _, _ =>
    ProveM.throw "DISJ_CASES: expected `p ∨ q`, `p ⇒ r`, `q ⇒ r`"

/-! ## Existential quantifier -/

def freshExQ : Name := "_ex_q"
def freshExX : Name := "_ex_x"

/-- `EXISTS`: from `Γ ⊢ P t` conclude `Γ ⊢ ∃ P`. -/
def existsIntro (α : Ty) (P t : Tm) (th : CertifiedThm env) :
    ProveM env (CertifiedThm env) := do
  let q := Tm.fvar freshExQ .bool
  let x := Tm.fvar freshExX α
  if P.freeIn freshExQ .bool || P.freeIn freshExX α || t.freeIn freshExQ .bool
      || t.freeIn freshExX α then
    ProveM.throw "EXISTS: reserved variable is free"
  unless th.concl == P.app t do
    ProveM.throw "EXISTS: expected `P t`"
  let hallx := Tm.all α ((Tm.imp (P.app x) q).abstract freshExX α)
  let th1 ← spec t (← assume hallx)
  let th2 ← mp th1 th
  let th3 ← disch hallx th2
  eqMp (← sym (← unfoldEx α P)) (← gen freshExQ .bool th3)

/-- `CHOOSE`: from `Γ ⊢ ∃ P` and `Δ ⊢ ∀ x. P x ⇒ q` conclude `Γ,Δ ⊢ q`. -/
def existsElim (q : Tm) (thex thall : CertifiedThm env) :
    ProveM env (CertifiedThm env) := do
  match destEx thex.concl with
  | none => ProveM.throw "CHOOSE: expected an existential"
  | some (α, P) =>
    mp (← spec q (← eqMp (← unfoldEx α P) thex)) thall

end Hol
end Prove
end HOLean
