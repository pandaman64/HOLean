/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Typing
import HOLean.Syntax.Logic
import HOLean.Elab.Term

/-!
# Defined logical connectives

HOL Light defines the remaining connectives from equality (Harrison / Andrews)
by *definitional extension* of the environment: each connective is a constant
plus the axiom `⊢ c = t`.  There is no δ-reduction; unfolding is `EQ_MP`.

```
T          ≔  (λ p. p) = (λ p. p)
p ∧ q      ≔  (λ f. f p q) = (λ f. f T T)
p ⇒ q      ≔  (p ∧ q) = p
∀ P        ≔  P = (λ x. T)
⊥          ≔  ∀ p. p
¬ p        ≔  p ⇒ ⊥
p ∨ q      ≔  ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
∃ P        ≔  ∀ q. (∀ x. P x ⇒ q) ⇒ q
ONE_ONE f  ≔  ∀ x y. f x = f y ⇒ x = y
ONTO f     ≔  ∀ y. ∃ x. y = f x
```

The term formers (`Tm.and`, …) live in `HOLean.Syntax.Logic`.  Closed
defining right-hand sides below are written with `hol_tm` / `hol_prop`
and locked to the raw `Tm` tree by `rfl`.
-/

namespace HOLean

namespace Tm

/-- Harrison / Andrews expansion of `T`. -/
def truExpand : Tm :=
  mkEq (.bool ↝ .bool) (.lam .bool (.bvar 0)) (.lam .bool (.bvar 0))

/-- Harrison / Andrews expansion of `p ∧ q`. -/
def andExpand (p q : Tm) : Tm :=
  mkEq (boolCombTy ↝ .bool)
    (.lam boolCombTy (.app (.app (.bvar 0) (p.shift 1 0)) (q.shift 1 0)))
    (.lam boolCombTy (.app (.app (.bvar 0) (tru.shift 1 0)) (tru.shift 1 0)))

/-- Harrison / Andrews expansion of `p ⇒ q`. -/
def impExpand (p q : Tm) : Tm :=
  mkEq .bool (p.and q) p

/-- Harrison / Andrews expansion of `∀ P`. -/
def allExpand (α : Ty) (P : Tm) : Tm :=
  mkEq (α ↝ .bool) P (.lam α tru)

/-- `T ≔ (λ p. p) = (λ p. p)`. -/
def truDef : Tm :=
  hol_prop((fun (p : Bool) => p) = (fun (p : Bool) => p))

/-- `λ p q. (λ f. f p q) = (λ f. f T T)`. -/
def andDef : Tm :=
  hol_tm(fun (p q : Bool) =>
    (fun (f : Bool → Bool → Bool) => f p q) =
    (fun (f : Bool → Bool → Bool) => f true true))

/-- `λ p q. (p ∧ q) = p`. -/
def impDef : Tm :=
  hol_tm(fun (p q : Prop) => (p ∧ q) = p)

/-- `λ P. P = (λ x. T)`.  `A` is the schematic `primTyVar`. -/
def allDef : Tm :=
  hol_tm(fun {A : Type} (P : A → Prop) => P = fun (_x : A) => True)

/-- `⊥ ≔ ∀ p. p`. -/
def falsumDef : Tm :=
  hol_prop(∀ p : Prop, p)

/-- `λ p. p ⇒ ⊥`.  Written as `→ False`, not `¬`, so we do not unfold `not`. -/
def notDef : Tm :=
  hol_tm(fun (p : Prop) => p → False)

/-- `λ p q. ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r`. -/
def orDef : Tm :=
  hol_tm(fun (p q : Prop) => ∀ r : Prop, (p → r) → (q → r) → r)

/-- `λ P. ∀ q. (∀ x. P x ⇒ q) ⇒ q`. -/
def exDef : Tm :=
  hol_tm(fun {A : Type} (P : A → Prop) => ∀ q : Prop, (∀ x : A, P x → q) → q)

/-- `λ f. ∀ x y. f x = f y ⇒ x = y`. -/
def oneOneDef : Tm :=
  hol_tm(fun {A B : Type} (f : A → B) => ∀ x y : A, f x = f y → x = y)

/-- `λ f. ∀ y. ∃ x. y = f x`. -/
def ontoDef : Tm :=
  hol_tm(fun {A B : Type} (f : A → B) => ∀ y : B, ∃ x : A, y = f x)

theorem truDef_eq : truDef = truExpand := rfl

theorem andDef_eq :
    andDef = .lam .bool (.lam .bool (andExpand (.bvar 1) (.bvar 0))) := rfl

theorem impDef_eq :
    impDef = .lam .bool (.lam .bool (impExpand (.bvar 1) (.bvar 0))) := rfl

theorem allDef_eq :
    allDef = .lam (.var primTyVar ↝ .bool) (allExpand (.var primTyVar) (.bvar 0)) :=
  rfl

theorem falsumDef_eq : falsumDef = all .bool (.lam .bool (.bvar 0)) := rfl

theorem notDef_eq : notDef = .lam .bool (imp (bvar 0) falsum) := rfl

theorem orDef_eq :
    orDef = .lam .bool (.lam .bool
      (all .bool (.lam .bool
        (imp (imp (bvar 2) (bvar 0)) (imp (imp (bvar 1) (bvar 0)) (bvar 0)))))) :=
  rfl

theorem exDef_eq :
    exDef = .lam (.var primTyVar ↝ .bool)
      (all .bool (.lam .bool
        (imp (all (.var primTyVar) (.lam (.var primTyVar)
          (imp ((bvar 2).app (bvar 0)) (bvar 1)))) (bvar 0)))) :=
  rfl

theorem oneOneDef_eq :
    oneOneDef = .lam (.var primTyVar ↝ .var primTyVarB)
      (all (.var primTyVar) (.lam (.var primTyVar)
        (all (.var primTyVar) (.lam (.var primTyVar)
          (imp (mkEq (.var primTyVarB) ((bvar 2).app (bvar 1)) ((bvar 2).app (bvar 0)))
            (mkEq (.var primTyVar) (bvar 1) (bvar 0))))))) :=
  rfl

theorem ontoDef_eq :
    ontoDef = .lam (.var primTyVar ↝ .var primTyVarB)
      (all (.var primTyVarB) (.lam (.var primTyVarB)
        (ex (.var primTyVar) (.lam (.var primTyVar)
          (mkEq (.var primTyVarB) (bvar 1) ((bvar 2).app (bvar 0))))))) :=
  rfl

end Tm

/-- The environment has the defined logical constants and their defining
equations. -/
class Env.HasConnectives (env : Env) extends Env.HasPrims env where
  tru_const : env.constants truName = some truTy
  and_const : env.constants andName = some andTy
  imp_const : env.constants impName = some impTy
  all_const : env.constants allName = some allTy
  falsum_const : env.constants falsumName = some falsumTy
  not_const : env.constants notName = some notTy
  or_const : env.constants orName = some orTy
  ex_const : env.constants exName = some exTy
  oneOne_const : env.constants oneOneName = some oneOneTy
  onto_const : env.constants ontoName = some ontoTy
  tru_ax : env.axioms (Tm.mkEq truTy Tm.tru Tm.truDef)
  and_ax : env.axioms (Tm.mkEq andTy (.const andName andTy) Tm.andDef)
  imp_ax : env.axioms (Tm.mkEq impTy (.const impName impTy) Tm.impDef)
  all_ax : env.axioms (Tm.mkEq allTy (.const allName allTy) Tm.allDef)
  falsum_ax : env.axioms (Tm.mkEq falsumTy Tm.falsum Tm.falsumDef)
  not_ax : env.axioms (Tm.mkEq notTy (.const notName notTy) Tm.notDef)
  or_ax : env.axioms (Tm.mkEq orTy (.const orName orTy) Tm.orDef)
  ex_ax : env.axioms (Tm.mkEq exTy (.const exName exTy) Tm.exDef)
  oneOne_ax : env.axioms (Tm.mkEq oneOneTy (.const oneOneName oneOneTy) Tm.oneOneDef)
  onto_ax : env.axioms (Tm.mkEq ontoTy (.const ontoName ontoTy) Tm.ontoDef)

variable {env : Env}

theorem HasType.tru [Env.HasConnectives env] {Γ} :
    HasType env Γ Tm.tru .bool :=
  HasType.const Env.HasConnectives.tru_const (Ty.isInstanceOf_self truTy)

theorem HasType.andConst [Env.HasConnectives env] {Γ} :
    HasType env Γ (.const andName andTy) andTy :=
  HasType.const Env.HasConnectives.and_const (Ty.isInstanceOf_self andTy)

theorem HasType.and [Env.HasConnectives env] {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.and q) .bool :=
  HasType.app (HasType.app HasType.andConst hp) hq

theorem HasType.impConst [Env.HasConnectives env] {Γ} :
    HasType env Γ (.const impName impTy) impTy :=
  HasType.const Env.HasConnectives.imp_const (Ty.isInstanceOf_self impTy)

theorem HasType.imp [Env.HasConnectives env] {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.imp q) .bool :=
  HasType.app (HasType.app HasType.impConst hp) hq

theorem HasType.allConst [Env.HasConnectives env] {Γ} (α : Ty) :
    HasType env Γ (.const allName ((α ↝ .bool) ↝ .bool)) ((α ↝ .bool) ↝ .bool) :=
  HasType.const Env.HasConnectives.all_const (allTy_isInstanceOf α)

theorem HasType.all [Env.HasConnectives env] {Γ α P}
    (hP : HasType env Γ P (α ↝ .bool)) :
    HasType env Γ (Tm.all α P) .bool :=
  HasType.app (HasType.allConst α) hP

theorem HasType.falsum [Env.HasConnectives env] {Γ} :
    HasType env Γ Tm.falsum .bool :=
  HasType.const Env.HasConnectives.falsum_const (Ty.isInstanceOf_self falsumTy)

theorem HasType.notConst [Env.HasConnectives env] {Γ} :
    HasType env Γ (.const notName notTy) notTy :=
  HasType.const Env.HasConnectives.not_const (Ty.isInstanceOf_self notTy)

theorem HasType.not [Env.HasConnectives env] {Γ p} (hp : HasType env Γ p .bool) :
    HasType env Γ p.not .bool :=
  HasType.app HasType.notConst hp

theorem HasType.orConst [Env.HasConnectives env] {Γ} :
    HasType env Γ (.const orName orTy) orTy :=
  HasType.const Env.HasConnectives.or_const (Ty.isInstanceOf_self orTy)

theorem HasType.or [Env.HasConnectives env] {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.or q) .bool :=
  HasType.app (HasType.app HasType.orConst hp) hq

theorem HasType.exConst [Env.HasConnectives env] {Γ} (α : Ty) :
    HasType env Γ (.const exName ((α ↝ .bool) ↝ .bool)) ((α ↝ .bool) ↝ .bool) :=
  HasType.const Env.HasConnectives.ex_const (exTy_isInstanceOf α)

theorem HasType.ex [Env.HasConnectives env] {Γ α P}
    (hP : HasType env Γ P (α ↝ .bool)) :
    HasType env Γ (Tm.ex α P) .bool :=
  HasType.app (HasType.exConst α) hP

theorem HasType.oneOneConst [Env.HasConnectives env] {Γ} (α β : Ty) :
    HasType env Γ (.const oneOneName ((α ↝ β) ↝ .bool)) ((α ↝ β) ↝ .bool) :=
  HasType.const Env.HasConnectives.oneOne_const (oneOneTy_isInstanceOf α β)

theorem HasType.oneOne [Env.HasConnectives env] {Γ α β f}
    (hf : HasType env Γ f (α ↝ β)) :
    HasType env Γ (Tm.oneOne α β f) .bool :=
  HasType.app (HasType.oneOneConst α β) hf

theorem HasType.ontoConst [Env.HasConnectives env] {Γ} (α β : Ty) :
    HasType env Γ (.const ontoName ((α ↝ β) ↝ .bool)) ((α ↝ β) ↝ .bool) :=
  HasType.const Env.HasConnectives.onto_const (ontoTy_isInstanceOf α β)

theorem HasType.onto [Env.HasConnectives env] {Γ α β f}
    (hf : HasType env Γ f (α ↝ β)) :
    HasType env Γ (Tm.onto α β f) .bool :=
  HasType.app (HasType.ontoConst α β) hf

theorem HasType.truExpand [Env.HasEq env] {Γ} :
    HasType env Γ Tm.truExpand .bool :=
  HasType.mkEq
    (HasType.lam (HasType.bvar (by simp)))
    (HasType.lam (HasType.bvar (by simp)))

theorem HasType.andExpand [Env.HasConnectives env] {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.andExpand q) .bool := by
  unfold Tm.andExpand Tm.boolCombTy
  apply HasType.mkEq
  · apply HasType.lam
    exact HasType.app
      (HasType.app (HasType.bvar (by simp)) (hp.shift0 _))
      (hq.shift0 _)
  · apply HasType.lam
    exact HasType.app
      (HasType.app (HasType.bvar (by simp)) (HasType.tru.shift0 _))
      (HasType.tru.shift0 _)

theorem HasType.impExpand [Env.HasConnectives env] {Γ p q}
    (hp : HasType env Γ p .bool) (hq : HasType env Γ q .bool) :
    HasType env Γ (p.impExpand q) .bool :=
  HasType.mkEq (HasType.and hp hq) hp

theorem HasType.allExpand [Env.HasConnectives env] {Γ α P}
    (hP : HasType env Γ P (α ↝ .bool)) :
    HasType env Γ (Tm.allExpand α P) .bool :=
  HasType.mkEq hP (HasType.lam HasType.tru)

theorem HasType.andDef [Env.HasConnectives env] :
    HasType env [] Tm.andDef andTy :=
  HasType.lam (HasType.lam (HasType.andExpand
    (HasType.bvar (by simp)) (HasType.bvar (by simp))))

theorem HasType.impDef [Env.HasConnectives env] :
    HasType env [] Tm.impDef impTy :=
  HasType.lam (HasType.lam (HasType.impExpand
    (HasType.bvar (by simp)) (HasType.bvar (by simp))))

theorem HasType.allDef [Env.HasConnectives env] :
    HasType env [] Tm.allDef allTy :=
  HasType.lam (HasType.allExpand (HasType.bvar (by simp)))

/-! Intermediate environments for the definitional chain. -/

def envTru : Env := holCore.addDef truName truTy Tm.truDef
def envAnd : Env := envTru.addDef andName andTy Tm.andDef
def envImp : Env := envAnd.addDef impName impTy Tm.impDef
def envAll : Env := envImp.addDef allName allTy Tm.allDef
def envFalsum : Env := envAll.addDef falsumName falsumTy Tm.falsumDef
def envNot : Env := envFalsum.addDef notName notTy Tm.notDef
def envOr : Env := envNot.addDef orName orTy Tm.orDef
def envEx : Env := envOr.addDef exName exTy Tm.exDef
def envOneOne : Env := envEx.addDef oneOneName oneOneTy Tm.oneOneDef

/-- Primitive constants plus the defined logical connectives. -/
def holLogic : Env := envOneOne.addDef ontoName ontoTy Tm.ontoDef

private theorem fresh_core {n : Name} (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    holCore.constants n = none :=
  holConstants_of_ne heq hsel

theorem envTru_constants_tru : envTru.constants truName = some truTy := by
  simp [envTru]

private theorem envTru_fresh {n : Name}
    (h : n ≠ truName) (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envTru.constants n = none := by
  simp [envTru, Env.addDef_constants_of_ne (h := h), fresh_core heq hsel]

theorem envAnd_constants_and : envAnd.constants andName = some andTy := by
  simp [envAnd]

private theorem envAnd_fresh {n : Name}
    (h1 : n ≠ andName) (h2 : n ≠ truName) (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envAnd.constants n = none := by
  simp [envAnd, Env.addDef_constants_of_ne (h := h1), envTru_fresh h2 heq hsel]

theorem envImp_constants_imp : envImp.constants impName = some impTy := by
  simp [envImp]

private theorem envImp_fresh {n : Name}
    (h1 : n ≠ impName) (h2 : n ≠ andName) (h3 : n ≠ truName)
    (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envImp.constants n = none := by
  simp [envImp, Env.addDef_constants_of_ne (h := h1), envAnd_fresh h2 h3 heq hsel]

theorem envAll_constants_all : envAll.constants allName = some allTy := by
  simp [envAll]

private theorem envAll_fresh {n : Name}
    (h1 : n ≠ allName) (h2 : n ≠ impName) (h3 : n ≠ andName) (h4 : n ≠ truName)
    (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envAll.constants n = none := by
  simp [envAll, Env.addDef_constants_of_ne (h := h1), envImp_fresh h2 h3 h4 heq hsel]

theorem envFalsum_constants_falsum : envFalsum.constants falsumName = some falsumTy := by
  simp [envFalsum]

private theorem envFalsum_fresh {n : Name}
    (h1 : n ≠ falsumName) (h2 : n ≠ allName) (h3 : n ≠ impName) (h4 : n ≠ andName)
    (h5 : n ≠ truName) (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envFalsum.constants n = none := by
  simp [envFalsum, Env.addDef_constants_of_ne (h := h1), envAll_fresh h2 h3 h4 h5 heq hsel]

theorem envNot_constants_not : envNot.constants notName = some notTy := by
  simp [envNot]

private theorem envNot_fresh {n : Name}
    (h1 : n ≠ notName) (h2 : n ≠ falsumName) (h3 : n ≠ allName) (h4 : n ≠ impName)
    (h5 : n ≠ andName) (h6 : n ≠ truName) (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envNot.constants n = none := by
  simp [envNot, Env.addDef_constants_of_ne (h := h1),
    envFalsum_fresh h2 h3 h4 h5 h6 heq hsel]

theorem envOr_constants_or : envOr.constants orName = some orTy := by
  simp [envOr]

private theorem envOr_fresh {n : Name}
    (h1 : n ≠ orName) (h2 : n ≠ notName) (h3 : n ≠ falsumName) (h4 : n ≠ allName)
    (h5 : n ≠ impName) (h6 : n ≠ andName) (h7 : n ≠ truName)
    (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envOr.constants n = none := by
  simp [envOr, Env.addDef_constants_of_ne (h := h1),
    envNot_fresh h2 h3 h4 h5 h6 h7 heq hsel]

theorem envEx_constants_ex : envEx.constants exName = some exTy := by
  simp [envEx]

private theorem envEx_fresh {n : Name}
    (h1 : n ≠ exName) (h2 : n ≠ orName) (h3 : n ≠ notName) (h4 : n ≠ falsumName)
    (h5 : n ≠ allName) (h6 : n ≠ impName) (h7 : n ≠ andName) (h8 : n ≠ truName)
    (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envEx.constants n = none := by
  simp [envEx, Env.addDef_constants_of_ne (h := h1),
    envOr_fresh h2 h3 h4 h5 h6 h7 h8 heq hsel]

theorem envOneOne_constants_oneOne : envOneOne.constants oneOneName = some oneOneTy := by
  simp [envOneOne]

private theorem envOneOne_fresh {n : Name}
    (h1 : n ≠ oneOneName) (h2 : n ≠ exName) (h3 : n ≠ orName) (h4 : n ≠ notName)
    (h5 : n ≠ falsumName) (h6 : n ≠ allName) (h7 : n ≠ impName) (h8 : n ≠ andName)
    (h9 : n ≠ truName) (heq : n ≠ eqName) (hsel : n ≠ selectName) :
    envOneOne.constants n = none := by
  simp [envOneOne, Env.addDef_constants_of_ne (h := h1),
    envEx_fresh h2 h3 h4 h5 h6 h7 h8 h9 heq hsel]

/-! Typing of defining right-hand sides in the environment that introduces them. -/

private theorem hasType_tru_in (e : Env)
    (h : e.constants truName = some truTy) {Γ} :
    HasType e Γ Tm.tru .bool :=
  HasType.const h (Ty.isInstanceOf_self truTy)

private theorem hasType_and_in (e : Env)
    (h : e.constants andName = some andTy) {Γ p q}
    (hp : HasType e Γ p .bool) (hq : HasType e Γ q .bool) :
    HasType e Γ (p.and q) .bool :=
  HasType.app (HasType.app (HasType.const h (Ty.isInstanceOf_self andTy)) hp) hq

private theorem hasType_imp_in (e : Env)
    (h : e.constants impName = some impTy) {Γ p q}
    (hp : HasType e Γ p .bool) (hq : HasType e Γ q .bool) :
    HasType e Γ (p.imp q) .bool :=
  HasType.app (HasType.app (HasType.const h (Ty.isInstanceOf_self impTy)) hp) hq

private theorem hasType_all_in (e : Env)
    (h : e.constants allName = some allTy) {Γ α P}
    (hP : HasType e Γ P (α ↝ .bool)) :
    HasType e Γ (Tm.all α P) .bool :=
  HasType.app (HasType.const h (allTy_isInstanceOf α)) hP

private theorem hasType_falsum_in (e : Env)
    (h : e.constants falsumName = some falsumTy) {Γ} :
    HasType e Γ Tm.falsum .bool :=
  HasType.const h (Ty.isInstanceOf_self falsumTy)

private theorem hasType_ex_in (e : Env)
    (h : e.constants exName = some exTy) {Γ α P}
    (hP : HasType e Γ P (α ↝ .bool)) :
    HasType e Γ (Tm.ex α P) .bool :=
  HasType.app (HasType.const h (exTy_isInstanceOf α)) hP

private theorem hasType_truDef (e : Env) [Env.HasEq e] :
    HasType e [] Tm.truDef .bool :=
  HasType.truExpand

private theorem htBvar0 {e : Env} {α : Ty} {Γ} :
    HasType e (α :: Γ) (Tm.bvar 0) α :=
  HasType.bvar (by simp)

private theorem htBvar1 {e : Env} {γ α : Ty} {Γ} :
    HasType e (γ :: α :: Γ) (Tm.bvar 1) α :=
  HasType.bvar (by simp)

private theorem htBvar2 {e : Env} {δ γ α : Ty} {Γ} :
    HasType e (δ :: γ :: α :: Γ) (Tm.bvar 2) α :=
  HasType.bvar (by simp)

private theorem hasType_andDef (e : Env) [Env.HasEq e]
    (htru : e.constants truName = some truTy) :
    HasType e [] Tm.andDef andTy := by
  rw [Tm.andDef_eq]
  unfold Tm.andExpand Tm.boolCombTy andTy
  refine HasType.lam (HasType.lam ?_)
  apply HasType.mkEq
  · apply HasType.lam
    exact HasType.app (HasType.app htBvar0 htBvar2) htBvar1
  · apply HasType.lam
    exact HasType.app
      (HasType.app htBvar0 ((hasType_tru_in e htru).shift0 _))
      ((hasType_tru_in e htru).shift0 _)

private theorem hasType_impDef (e : Env) [Env.HasEq e]
    (hand : e.constants andName = some andTy) :
    HasType e [] Tm.impDef impTy := by
  rw [Tm.impDef_eq]
  unfold Tm.impExpand impTy
  refine HasType.lam (HasType.lam ?_)
  exact HasType.mkEq (hasType_and_in e hand htBvar1 htBvar0) htBvar1

private theorem hasType_allDef (e : Env) [Env.HasEq e]
    (htru : e.constants truName = some truTy) :
    HasType e [] Tm.allDef allTy := by
  rw [Tm.allDef_eq]
  unfold Tm.allExpand allTy
  refine HasType.lam ?_
  exact HasType.mkEq (HasType.bvar (by simp))
    (HasType.lam (hasType_tru_in e htru))

private theorem hasType_falsumDef (e : Env)
    (hall : e.constants allName = some allTy) :
    HasType e [] Tm.falsumDef .bool :=
  hasType_all_in e hall (HasType.lam (HasType.bvar (by simp)))

private theorem hasType_notDef (e : Env)
    (himp : e.constants impName = some impTy)
    (hfals : e.constants falsumName = some falsumTy) :
    HasType e [] Tm.notDef notTy := by
  rw [Tm.notDef_eq]
  unfold notTy
  refine HasType.lam ?_
  exact hasType_imp_in e himp (HasType.bvar (by simp)) (hasType_falsum_in e hfals)

private theorem hasType_orDef (e : Env)
    (hall : e.constants allName = some allTy)
    (himp : e.constants impName = some impTy) :
    HasType e [] Tm.orDef orTy := by
  rw [Tm.orDef_eq]
  unfold orTy
  refine HasType.lam (HasType.lam ?_)
  refine hasType_all_in e hall (HasType.lam ?_)
  refine hasType_imp_in e himp
    (hasType_imp_in e himp (HasType.bvar (by simp)) (HasType.bvar (by simp))) ?_
  refine hasType_imp_in e himp
    (hasType_imp_in e himp (HasType.bvar (by simp)) (HasType.bvar (by simp))) ?_
  exact HasType.bvar (by simp)

private theorem hasType_exDef (e : Env)
    (hall : e.constants allName = some allTy)
    (himp : e.constants impName = some impTy) :
    HasType e [] Tm.exDef exTy := by
  rw [Tm.exDef_eq]
  unfold exTy
  refine HasType.lam ?_
  refine hasType_all_in e hall (HasType.lam ?_)
  refine hasType_imp_in e himp ?_ (HasType.bvar (by simp))
  refine hasType_all_in e hall (HasType.lam ?_)
  refine hasType_imp_in e himp ?_ (HasType.bvar (by simp))
  exact HasType.app (α := .var primTyVar) htBvar2 htBvar0

private theorem hasType_oneOneDef (e : Env) [Env.HasEq e]
    (hall : e.constants allName = some allTy)
    (himp : e.constants impName = some impTy) :
    HasType e [] Tm.oneOneDef oneOneTy := by
  rw [Tm.oneOneDef_eq]
  unfold oneOneTy
  refine HasType.lam ?_
  refine hasType_all_in e hall (HasType.lam ?_)
  refine hasType_all_in e hall (HasType.lam ?_)
  refine hasType_imp_in e himp ?_ (HasType.mkEq (α := .var primTyVar) htBvar1 htBvar0)
  exact HasType.mkEq (α := .var primTyVarB)
    (HasType.app (α := .var primTyVar) htBvar2 htBvar1)
    (HasType.app (α := .var primTyVar) htBvar2 htBvar0)

private theorem hasType_ontoDef (e : Env) [Env.HasEq e]
    (hall : e.constants allName = some allTy)
    (hex : e.constants exName = some exTy) :
    HasType e [] Tm.ontoDef ontoTy := by
  rw [Tm.ontoDef_eq]
  unfold ontoTy
  refine HasType.lam ?_
  refine hasType_all_in e hall (HasType.lam ?_)
  refine hasType_ex_in e hex (HasType.lam ?_)
  exact HasType.mkEq (α := .var primTyVarB) htBvar1
    (HasType.app (α := .var primTyVar) htBvar2 htBvar0)

/-! Carry constants along the chain. -/

private theorem carry {e : Env} {n m : Name} {ty ty' : Ty} {rhs : Tm}
    (h : e.constants n = some ty) (hne : n ≠ m) :
    (e.addDef m ty' rhs).constants n = some ty :=
  (Env.addDef_constants_of_ne e ty' rhs hne).trans h

private theorem envTru_tru : envTru.constants truName = some truTy :=
  envTru_constants_tru

private theorem envAnd_tru : envAnd.constants truName = some truTy :=
  carry envTru_tru (by decide)

private theorem envImp_tru : envImp.constants truName = some truTy :=
  carry envAnd_tru (by decide)

private theorem envImp_and : envImp.constants andName = some andTy :=
  carry envAnd_constants_and (by decide)

private theorem envAll_tru : envAll.constants truName = some truTy :=
  carry envImp_tru (by decide)

private theorem envAll_and : envAll.constants andName = some andTy :=
  carry envImp_and (by decide)

private theorem envAll_imp : envAll.constants impName = some impTy :=
  carry envImp_constants_imp (by decide)

private theorem envFalsum_all : envFalsum.constants allName = some allTy :=
  carry envAll_constants_all (by decide)

private theorem envFalsum_imp : envFalsum.constants impName = some impTy :=
  carry envAll_imp (by decide)

private theorem envNot_imp : envNot.constants impName = some impTy :=
  carry envFalsum_imp (by decide)

private theorem envNot_all : envNot.constants allName = some allTy :=
  carry envFalsum_all (by decide)

private theorem envNot_falsum : envNot.constants falsumName = some falsumTy :=
  carry envFalsum_constants_falsum (by decide)

private theorem envOr_all : envOr.constants allName = some allTy :=
  carry envNot_all (by decide)

private theorem envOr_imp : envOr.constants impName = some impTy :=
  carry envNot_imp (by decide)

private theorem envEx_all : envEx.constants allName = some allTy :=
  carry envOr_all (by decide)

private theorem envEx_imp : envEx.constants impName = some impTy :=
  carry envOr_imp (by decide)

private theorem envOneOne_all : envOneOne.constants allName = some allTy :=
  carry envEx_all (by decide)

private theorem envOneOne_ex : envOneOne.constants exName = some exTy :=
  carry envEx_constants_ex (by decide)

private theorem envFalsum_tru : envFalsum.constants truName = some truTy :=
  carry envAll_tru (by decide)
private theorem envNot_tru : envNot.constants truName = some truTy :=
  carry envFalsum_tru (by decide)
private theorem envOr_tru : envOr.constants truName = some truTy :=
  carry envNot_tru (by decide)
private theorem envEx_tru : envEx.constants truName = some truTy :=
  carry envOr_tru (by decide)
private theorem envOneOne_tru : envOneOne.constants truName = some truTy :=
  carry envEx_tru (by decide)

private theorem envFalsum_and : envFalsum.constants andName = some andTy :=
  carry envAll_and (by decide)
private theorem envNot_and : envNot.constants andName = some andTy :=
  carry envFalsum_and (by decide)
private theorem envOr_and : envOr.constants andName = some andTy :=
  carry envNot_and (by decide)
private theorem envEx_and : envEx.constants andName = some andTy :=
  carry envOr_and (by decide)
private theorem envOneOne_and : envOneOne.constants andName = some andTy :=
  carry envEx_and (by decide)

private theorem envOneOne_imp : envOneOne.constants impName = some impTy :=
  carry envEx_imp (by decide)

private theorem envOr_falsum : envOr.constants falsumName = some falsumTy :=
  carry envNot_falsum (by decide)
private theorem envEx_falsum : envEx.constants falsumName = some falsumTy :=
  carry envOr_falsum (by decide)
private theorem envOneOne_falsum : envOneOne.constants falsumName = some falsumTy :=
  carry envEx_falsum (by decide)

private theorem envOr_not : envOr.constants notName = some notTy :=
  carry envNot_constants_not (by decide)
private theorem envEx_not : envEx.constants notName = some notTy :=
  carry envOr_not (by decide)
private theorem envOneOne_not : envOneOne.constants notName = some notTy :=
  carry envEx_not (by decide)

private theorem envEx_or : envEx.constants orName = some orTy :=
  carry envOr_constants_or (by decide)
private theorem envOneOne_or : envOneOne.constants orName = some orTy :=
  carry envEx_or (by decide)

instance : Env.HasEq envTru := Env.HasEq.addDef (by decide)
instance : Env.HasEq envAnd := Env.HasEq.addDef (by decide)
instance : Env.HasEq envImp := Env.HasEq.addDef (by decide)
instance : Env.HasEq envAll := Env.HasEq.addDef (by decide)
instance : Env.HasEq envFalsum := Env.HasEq.addDef (by decide)
instance : Env.HasEq envNot := Env.HasEq.addDef (by decide)
instance : Env.HasEq envOr := Env.HasEq.addDef (by decide)
instance : Env.HasEq envEx := Env.HasEq.addDef (by decide)
instance : Env.HasEq envOneOne := Env.HasEq.addDef (by decide)
instance : Env.HasEq holLogic := Env.HasEq.addDef (by decide)

instance : Env.HasSelect envTru := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envAnd := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envImp := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envAll := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envFalsum := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envNot := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envOr := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envEx := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect envOneOne := Env.HasSelect.addDef (by decide)
instance : Env.HasSelect holLogic := Env.HasSelect.addDef (by decide)

theorem holCore_WF : holCore.WF := fun _ h => False.elim h

theorem envTru_WF : envTru.WF :=
  holCore_WF.addDef (fresh_core (by decide) (by decide))
    (by decide) (hasType_truDef holCore)

theorem envAnd_WF : envAnd.WF :=
  envTru_WF.addDef (envTru_fresh (by decide) (by decide) (by decide))
    (by decide) (hasType_andDef envTru envTru_tru)

theorem envImp_WF : envImp.WF :=
  envAnd_WF.addDef (envAnd_fresh (by decide) (by decide) (by decide) (by decide))
    (by decide) (hasType_impDef envAnd envAnd_constants_and)

theorem envAll_WF : envAll.WF :=
  envImp_WF.addDef
    (envImp_fresh (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide) (hasType_allDef envImp envImp_tru)

theorem envFalsum_WF : envFalsum.WF :=
  envAll_WF.addDef
    (envAll_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (by decide) (hasType_falsumDef envAll envAll_constants_all)

theorem envNot_WF : envNot.WF :=
  envFalsum_WF.addDef
    (envFalsum_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (by decide)
    (hasType_notDef envFalsum envFalsum_imp envFalsum_constants_falsum)

theorem envOr_WF : envOr.WF :=
  envNot_WF.addDef
    (envNot_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))
    (by decide) (hasType_orDef envNot envNot_all envNot_imp)

theorem envEx_WF : envEx.WF :=
  envOr_WF.addDef
    (envOr_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))
    (by decide) (hasType_exDef envOr envOr_all envOr_imp)

theorem envOneOne_WF : envOneOne.WF :=
  envEx_WF.addDef
    (envEx_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide)
    (hasType_oneOneDef envEx envEx_all envEx_imp)

theorem holLogic_WF : holLogic.WF :=
  envOneOne_WF.addDef
    (envOneOne_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide)
    (hasType_ontoDef envOneOne envOneOne_all envOneOne_ex)

/-! `holLogic` has every connective constant and defining axiom. -/

private theorem holLogic_const (n : Name) (ty : Ty)
    (h : envOneOne.constants n = some ty) (hne : n ≠ ontoName := by decide) :
    holLogic.constants n = some ty := by
  simpa [holLogic, Env.addDef_constants_of_ne (h := hne)] using h

private theorem holLogic_ax {ax : Tm} (h : envOneOne.axioms ax) :
    holLogic.axioms ax :=
  Env.addDef_axioms_of h

instance : Env.HasPrims holLogic where

theorem holCore_le_holLogic : holCore.LE holLogic :=
  ⟨fun n ty h => by
      simp [holCore] at h
      by_cases heq : n = eqName
      · subst heq
        simp [holConstants] at h
        cases h
        exact Env.HasEq.eq_const (env := holLogic)
      · by_cases hsel : n = selectName
        · subst hsel
          simp [holConstants, show selectName ≠ eqName from eqName_ne_selectName.symm] at h
          cases h
          exact Env.HasSelect.select_const (env := holLogic)
        · simp [holConstants, heq, hsel] at h,
   fun _ h => False.elim h⟩

instance : Env.HasConnectives holLogic where
  tru_const := holLogic_const truName truTy envOneOne_tru
  and_const := holLogic_const andName andTy envOneOne_and
  imp_const := holLogic_const impName impTy envOneOne_imp
  all_const := holLogic_const allName allTy envOneOne_all
  falsum_const := holLogic_const falsumName falsumTy envOneOne_falsum
  not_const := holLogic_const notName notTy envOneOne_not
  or_const := holLogic_const orName orTy envOneOne_or
  ex_const := holLogic_const exName exTy envOneOne_ex
  oneOne_const := holLogic_const oneOneName oneOneTy envOneOne_constants_oneOne
  onto_const := by simp [holLogic]
  tru_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self holCore truName truTy Tm.truDef
  and_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envTru andName andTy Tm.andDef
  imp_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envAnd impName impTy Tm.impDef
  all_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envImp allName allTy Tm.allDef
  falsum_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envAll falsumName falsumTy Tm.falsumDef
  not_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envFalsum notName notTy Tm.notDef
  or_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envNot orName orTy Tm.orDef
  ex_ax :=
    holLogic_ax <|
      Env.addDef_axioms_of <|
      Env.addDef_axioms_self envOr exName exTy Tm.exDef
  oneOne_ax :=
    holLogic_ax <|
      Env.addDef_axioms_self envEx oneOneName oneOneTy Tm.oneOneDef
  onto_ax := Env.addDef_axioms_self envOneOne ontoName ontoTy Tm.ontoDef

/-! Public typing of each defining right-hand side in the environment
that introduces it (for model transport along the `addDef` chain). -/

theorem HasType.truDef_holCore : HasType holCore [] Tm.truDef truTy :=
  hasType_truDef holCore

theorem HasType.andDef_envTru : HasType envTru [] Tm.andDef andTy :=
  hasType_andDef envTru envTru_tru

theorem HasType.impDef_envAnd : HasType envAnd [] Tm.impDef impTy :=
  hasType_impDef envAnd envAnd_constants_and

theorem HasType.allDef_envImp : HasType envImp [] Tm.allDef allTy :=
  hasType_allDef envImp envImp_tru

theorem HasType.falsumDef_envAll : HasType envAll [] Tm.falsumDef falsumTy :=
  hasType_falsumDef envAll envAll_constants_all

theorem HasType.notDef_envFalsum : HasType envFalsum [] Tm.notDef notTy :=
  hasType_notDef envFalsum envFalsum_imp envFalsum_constants_falsum

theorem HasType.orDef_envNot : HasType envNot [] Tm.orDef orTy :=
  hasType_orDef envNot envNot_all envNot_imp

theorem HasType.exDef_envOr : HasType envOr [] Tm.exDef exTy :=
  hasType_exDef envOr envOr_all envOr_imp

theorem HasType.oneOneDef_envEx : HasType envEx [] Tm.oneOneDef oneOneTy :=
  hasType_oneOneDef envEx envEx_all envEx_imp

theorem HasType.ontoDef_envOneOne : HasType envOneOne [] Tm.ontoDef ontoTy :=
  hasType_ontoDef envOneOne envOneOne_all envOneOne_ex

theorem truName_fresh_core : holCore.constants truName = none :=
  fresh_core (by decide) (by decide)

theorem andName_fresh_envTru : envTru.constants andName = none :=
  envTru_fresh (by decide) (by decide) (by decide)

theorem impName_fresh_envAnd : envAnd.constants impName = none :=
  envAnd_fresh (by decide) (by decide) (by decide) (by decide)

theorem allName_fresh_envImp : envImp.constants allName = none :=
  envImp_fresh (by decide) (by decide) (by decide) (by decide) (by decide)

theorem falsumName_fresh_envAll : envAll.constants falsumName = none :=
  envAll_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem notName_fresh_envFalsum : envFalsum.constants notName = none :=
  envFalsum_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

theorem orName_fresh_envNot : envNot.constants orName = none :=
  envNot_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem exName_fresh_envOr : envOr.constants exName = none :=
  envOr_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem oneOneName_fresh_envEx : envEx.constants oneOneName = none :=
  envEx_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem ontoName_fresh_envOneOne : envOneOne.constants ontoName = none :=
  envOneOne_fresh (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! Names reserved for primitives and defined connectives (used by the elaborator). -/

def connectiveAndPrimNames : List Name :=
  [eqName, selectName, truName, andName, impName, allName, falsumName,
    notName, orName, exName, oneOneName, ontoName]

/-- A user constant name is not one of the primitive / connective names. -/
def nameNotInConnectiveAndPrim (n : Name) : Prop :=
  ∀ m ∈ connectiveAndPrimNames, n ≠ m

theorem nameNotInConnectiveAndPrim_of_decide (n : Name)
    (h : decide (∀ m ∈ connectiveAndPrimNames, n ≠ m) = true) :
    nameNotInConnectiveAndPrim n := by
  simp [nameNotInConnectiveAndPrim, List.all_eq_true] at h
  exact h

theorem mem_connectiveAndPrimNames_tru :
    truName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_and :
    andName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_imp :
    impName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_all :
    allName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_falsum :
    falsumName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_not :
    notName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_or :
    orName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_ex :
    exName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_oneOne :
    oneOneName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem mem_connectiveAndPrimNames_onto :
    ontoName ∈ connectiveAndPrimNames := by simp [connectiveAndPrimNames]

theorem Env.HasConnectives.addAxiom [Env.HasConnectives env] (ax : Tm) :
    Env.HasConnectives (env.addAxiom ax) where
  eq_const := by rw [Env.addAxiom_constants]; exact HasEq.eq_const
  select_const := by rw [Env.addAxiom_constants]; exact HasSelect.select_const
  tru_const := by rw [Env.addAxiom_constants]; exact HasConnectives.tru_const
  and_const := by rw [Env.addAxiom_constants]; exact HasConnectives.and_const
  imp_const := by rw [Env.addAxiom_constants]; exact HasConnectives.imp_const
  all_const := by rw [Env.addAxiom_constants]; exact HasConnectives.all_const
  falsum_const := by rw [Env.addAxiom_constants]; exact HasConnectives.falsum_const
  not_const := by rw [Env.addAxiom_constants]; exact HasConnectives.not_const
  or_const := by rw [Env.addAxiom_constants]; exact HasConnectives.or_const
  ex_const := by rw [Env.addAxiom_constants]; exact HasConnectives.ex_const
  oneOne_const := by rw [Env.addAxiom_constants]; exact HasConnectives.oneOne_const
  onto_const := by rw [Env.addAxiom_constants]; exact HasConnectives.onto_const
  tru_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq truTy Tm.tru Tm.truDef)
    (Env.HasConnectives.tru_ax (env := env))
  and_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq andTy (.const andName andTy) Tm.andDef)
    (Env.HasConnectives.and_ax (env := env))
  imp_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq impTy (.const impName impTy) Tm.impDef)
    (Env.HasConnectives.imp_ax (env := env))
  all_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq allTy (.const allName allTy) Tm.allDef)
    (Env.HasConnectives.all_ax (env := env))
  falsum_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq falsumTy Tm.falsum Tm.falsumDef)
    (Env.HasConnectives.falsum_ax (env := env))
  not_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq notTy (.const notName notTy) Tm.notDef)
    (Env.HasConnectives.not_ax (env := env))
  or_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq orTy (.const orName orTy) Tm.orDef)
    (Env.HasConnectives.or_ax (env := env))
  ex_ax := Env.addAxiom_axioms_of (env := env) ax (Tm.mkEq exTy (.const exName exTy) Tm.exDef)
    (Env.HasConnectives.ex_ax (env := env))
  oneOne_ax := Env.addAxiom_axioms_of (env := env) ax
    (Tm.mkEq oneOneTy (.const oneOneName oneOneTy) Tm.oneOneDef)
    (Env.HasConnectives.oneOne_ax (env := env))
  onto_ax := Env.addAxiom_axioms_of (env := env) ax
    (Tm.mkEq ontoTy (.const ontoName ontoTy) Tm.ontoDef)
    (Env.HasConnectives.onto_ax (env := env))

theorem Env.HasConnectives.addDef [Env.HasConnectives env] {n : Name} {ty : Ty} {rhs : Tm}
    (_hfresh : env.constants n = none) (hnames : nameNotInConnectiveAndPrim n) :
    Env.HasConnectives (env.addDef n ty rhs) where
  eq_const := by
    have hne : eqName ≠ n := (hnames eqName (by simp [connectiveAndPrimNames])).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := eqName) hne]
    exact HasEq.eq_const
  select_const := by
    have hne : selectName ≠ n := (hnames selectName (by simp [connectiveAndPrimNames])).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := selectName) hne]
    exact HasSelect.select_const
  tru_const := by
    have hne : truName ≠ n := (hnames truName mem_connectiveAndPrimNames_tru).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := truName) hne]
    exact HasConnectives.tru_const
  and_const := by
    have hne : andName ≠ n := (hnames andName mem_connectiveAndPrimNames_and).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := andName) hne]
    exact HasConnectives.and_const
  imp_const := by
    have hne : impName ≠ n := (hnames impName mem_connectiveAndPrimNames_imp).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := impName) hne]
    exact HasConnectives.imp_const
  all_const := by
    have hne : allName ≠ n := (hnames allName mem_connectiveAndPrimNames_all).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := allName) hne]
    exact HasConnectives.all_const
  falsum_const := by
    have hne : falsumName ≠ n := (hnames falsumName mem_connectiveAndPrimNames_falsum).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := falsumName) hne]
    exact HasConnectives.falsum_const
  not_const := by
    have hne : notName ≠ n := (hnames notName mem_connectiveAndPrimNames_not).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := notName) hne]
    exact HasConnectives.not_const
  or_const := by
    have hne : orName ≠ n := (hnames orName mem_connectiveAndPrimNames_or).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := orName) hne]
    exact HasConnectives.or_const
  ex_const := by
    have hne : exName ≠ n := (hnames exName mem_connectiveAndPrimNames_ex).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := exName) hne]
    exact HasConnectives.ex_const
  oneOne_const := by
    have hne : oneOneName ≠ n := (hnames oneOneName mem_connectiveAndPrimNames_oneOne).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := oneOneName) hne]
    exact HasConnectives.oneOne_const
  onto_const := by
    have hne : ontoName ≠ n := (hnames ontoName mem_connectiveAndPrimNames_onto).symm
    rw [Env.addDef_constants_of_ne env ty rhs (n := n) (m := ontoName) hne]
    exact HasConnectives.onto_const
  tru_ax := Env.addDef_axioms_of HasConnectives.tru_ax
  and_ax := Env.addDef_axioms_of HasConnectives.and_ax
  imp_ax := Env.addDef_axioms_of HasConnectives.imp_ax
  all_ax := Env.addDef_axioms_of HasConnectives.all_ax
  falsum_ax := Env.addDef_axioms_of HasConnectives.falsum_ax
  not_ax := Env.addDef_axioms_of HasConnectives.not_ax
  or_ax := Env.addDef_axioms_of HasConnectives.or_ax
  ex_ax := Env.addDef_axioms_of HasConnectives.ex_ax
  oneOne_ax := Env.addDef_axioms_of HasConnectives.oneOne_ax
  onto_ax := Env.addDef_axioms_of HasConnectives.onto_ax

end HOLean
