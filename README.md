# HOLean

A Lean 4 formalization of **Higher-Order Logic** — Church's Simple Type Theory
with schematic (ML-style) polymorphism — in the style of the HOL Light kernel.
The long-term goal is a **set-theoretic consistency proof**: interpret the
object logic in Mathlib's [`ZFSet`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html)
and conclude `⊬ ⊥`.

This repository currently defines the syntax, the type theory, and the
inference system, interprets them in Mathlib's `ZFSet`, and proves that
every `holEnv` theorem denotes `zfTrue`, so `⊬ ⊥`.

## Why this dialect

HOL is a family, not a single calculus.  We follow **HOL Light**
(`fusion.ml`) rather than HOL4's larger kernel or Isabelle/HOL's Pure
metalogic, because the kernel is small enough to study and to model:

| Layer | Contents |
| --- | --- |
| Types | schematic type variables, `bool`, `ind`, `α ↝ β` |
| Terms | variables, constants, application, λ |
| Logic primitives | equality `=`; later Hilbert `ε` |
| Inference | ten rules (below) |
| Axioms | η, choice, infinity |

Isabelle/HOL and HOL4 are definitional extensions of essentially this core
(plus richer architecture: locales, type classes, a bigger kernel).  A
consistency proof for the HOL Light core is the standard first target
(Harrison; Kumar–Arthan–Myreen–Owens / Candle).

Polymorphism is **schematic**, not System F: type variables are implicitly
∀-quantified at the theorem level and instantiated by `INST_TYPE`.  There
are no type lambdas in terms.

## Module map

```
HOLean/
  Syntax/Ty.lean       simple types, substitution, `isInstanceOf` / `matchTy`
  Syntax/Const.lean    names and generic types of `eq`, `select`
  Syntax/Tm.lean       locally nameless terms, shift / LC / open–close
  Syntax/Logic.lean    connective names / `Tm.and` formers (no elaborator)
  Env.lean             `Env` (constants × axioms), `addDef`, `holCore`
  Typing.lean          `HasType env`, `Env.WF`, inference, substitution lemmas
  Connective.lean      T, ∧, ⇒, ∀, ⊥, ¬, ∨, ∃, ONE_ONE, ONTO as `addDef`
  Kernel.lean          ten HOL Light rules plus `Provable.ax`
  Derived.lean         SYM, GEN, CONJ, projections, MP, weakening
  Axiom.lean           η / SELECT / INFINITY; `holEnv` over `holLogic`
  Elab/Translate.lean  `Lean.Expr` → `Ty` / `Tm`, filtered by sort
  Elab/Term.lean       `hol_ty(…)` / `hol_tm(…)` / `hol_prop(…)` / `hol(…)`
  Elab/Command.lean    `#hol` (needs `holEnv`, so it sits above `Axiom`)
  Model/Basic.lean     `zfBool`, graph application, `succ` on `omega`
  Model/Ty.lean        `Ty.denote`, `INST_TYPE` commutation
  Model/Const.lean     `eq` / `select` graphs
  Model/Tm.lean        `Tm.denote`, `HasType.denote_mem`, `EnvInterp.holCore`
  Model/Commute.lean   denotation commutes with open / close / `instTy` / subst
  Model/Sound.lean     `EnvModel`, `Provable.sound`, `Provable.sound_holCore`
  Model/Def.lean       `EnvModel.addDef`, `EnvModel.holLogic`
  Model/Logic.lean     connective truth tables in a `HasConnectives` model
  Model/Axiom.lean     `EnvModel.holEnv`, `¬ [] ⊩[holEnv] ⊥`
```

See `docs/MODEL.md` for the full standard-model plan.

Syntax through `Axiom` do not import Mathlib.  `HOLean.Elab` imports the Lean
compiler library (not Mathlib).  `HOLean.Model` is the first module that
imports Mathlib (`ZFSet.funs`, `omega`, `choice`).

## Design decisions

### Extrinsic typing

Terms are raw (`Tm`); `HasType Γ t α` is a judgment.  This matches HOL Light
and makes `INST_TYPE` a function on raw syntax.  An intrinsically typed
encoding (`Tm : Ty → Type`) fights type substitution, which *changes* the
index.

A term well-typed in the empty bound context is automatically locally
closed: there is no way to type an unbound `bvar`.

### Locally nameless terms

Free variables are HOL pairs `(name, type)` — `x:bool` and `x:ind` are
different variables.  Binders are de Bruijn indices.

This eliminates HOL Light's `Clash` during type instantiation: instantiating
`A ↦ bool` cannot capture a free `x:bool` by a binder that used to be
`x:A`, because the binder is an index.

α-equivalent named terms are **identical** as `Tm` values.  There is no
separate α-equivalence relation: `open (close x t) = t` when `t` is locally
closed, and `close (open x t) = t` when `x` is fresh.

### Environments (Lean4Lean-style, no δ)

Judgments are relative to an environment

```
Env  ≔  constants : Name → Option Ty     -- generic types
      × axioms    : Tm → Prop            -- closed booleans
```

This is the HOL analogue of Lean4Lean's `VEnv` (`constants` + `defeqs`).
HOL Light has no δ-reduction, so there is no independent definitional
equality: a definition is the axiom `⊢ c = t`, and unfolding is `EQ_MP`
or rewriting.

A term `const n inst` stores the *instantiated* type.  It is well-typed
when `env.constants n = some gen` and `gen.isInstanceOf inst`.
`HasType` reads only `constants`, never `axioms`.  That lets us layer
environments without a cycle: `holCore` is `{eq, select}` with no axioms;
`holLogic` is the definitional chain of connectives; `HOLAxiom` is typed
against `holLogic`; `holEnv` is `holLogic` plus η / SELECT / INFINITY.

`eq` and `select` are the initial constants.  User constants are
`Env.addConst` / `Env.addAxiom` / `Env.addDef`.  Connectives are
definitional extensions (`addDef`), not Lean term formers.
Type-level `new_basic_type_definition` is later.

**`Env.WF`.**  An environment is well-formed when every axiom is a closed
boolean in that signature (`HasType env [] p .bool`): only declared
constants, no dangling `bvar`s, type `bool`.  The constant table has no
extra check — every `Ty` is a valid generic type.  `holCore` is WF (no
axioms); `addDef` preserves WF; `holLogic` and `holEnv` are proved WF.
`Provable.of_axiom` turns `env.WF` plus `env.axioms p` into `[] ⊩[env] p`.

### Lean frontend

`hol_ty(…)`, `hol_tm(…)`, `hol_prop(…)`, and `hol(…)` reuse Lean's elaborator.
The resulting `Lean.Expr` is classified by the sort of its type and then
walked into `Ty` / `Tm`:

| Lean sort of `e` | HOL |
| --- | --- |
| `e : Type u` | type (`Ty`), if it is simple |
| `e : Prop` | proposition (`Tm` of type `bool`) |
| otherwise | term (`Tm`) |

Dependent types are rejected: a `Π (x : α), β` whose *type* body mentions
`x` is not a HOL type.  A `∀ (x : α), p` whose body is a proposition is a
quantifier (or `p ⇒ q` when `α : Prop` and `q` ignores the proof).
`Type`-binders become schematic type variables, not type lambdas.
`Prop`/`Bool` stand for `bool`; `Nat`/`Ind` stand for `ind`.  Lean
connectives (`∧`, `∨`, `¬`, `=`, `∀`, `∃`, `Classical.epsilon`) map to
the `holLogic` constants.

Closed defining right-hand sides (`Tm.andDef`, `infinityAxiom`, …) are
themselves written with `hol_tm` / `hol_prop`.  That is not circular:
names and formers live in `Syntax/Logic.lean` (no elaborator), the
elaborator imports only that file, and `Connective` / `Axiom` import the
elaborator.  Parameterized formers (`andExpand p q`, `etaAxiom α β f`)
stay as functions on `Tm` — they would need antiquotation.

### Lists as hypothesis sets

`Provable env` stores hypotheses as `List Tm`.  The rules use `++` and
`hypsErase`; validity does not depend on order or duplicates.  A later
cleanup can switch to `Finset` once we import Mathlib in the kernel.

## The inference system

```
REFL                 ⊢ t = t
TRANS                Γ ⊢ s = t    Δ ⊢ t = u          ⇒  Γ,Δ ⊢ s = u
MK_COMB              Γ ⊢ f = g    Δ ⊢ x = y          ⇒  Γ,Δ ⊢ f x = g y
ABS (x ∉ FV(Γ))      Γ ⊢ s = t                       ⇒  Γ ⊢ (λx. s) = (λx. t)
BETA                 ⊢ ((λx. t) x) = t
ASSUME (p : bool)    {p} ⊢ p
EQ_MP                Γ ⊢ p = q    Δ ⊢ p              ⇒  Γ,Δ ⊢ q
DEDUCT_ANTISYM       Γ ⊢ p        Δ ⊢ q              ⇒  Γ\{q}, Δ\{p} ⊢ p = q
INST_TYPE θ          Γ ⊢ p                           ⇒  Γ[θ] ⊢ p[θ]
INST σ               Γ ⊢ p                           ⇒  Γ[σ] ⊢ p[σ]
```

`Provable.bool_typed` shows every derivable sequent has closed boolean
hypotheses and a closed boolean conclusion.  Rules that form equations
need `Env.HasEq`.  `Provable.ax` admits a closed environment axiom;
`Provable.of_axiom` does so from `env.WF`.  The notation is
`Γ ⊩[env] p` for `Provable env Γ p`.

`ABS` still requires `x ∉ FV(Γ)`: locally nameless syntax removes binder
clash, not hypothesis freshness.  Bound contexts are ordinary lists
(`Γ[i]?`, `Γ.insertIdx c γ`).

Derived rules that go through `DEDUCT_ANTISYM` against `⊢ T` ask for
`T ∉ Γ` so the hypothesis list stays `Γ` rather than `Γ \ {T}`.

Defined connectives are **object-language constants** installed by
`Env.addDef` (`⊢ c = t`; unfolding is `EQ_MP`, there is no δ).  The
Harrison / Andrews expansions are the defining right-hand sides:

```
T          ≔  (λp. p) = (λp. p)
p ∧ q      ≔  (λf. f p q) = (λf. f T T)
p ⇒ q      ≔  (p ∧ q) = p
∀ P        ≔  P = (λx. T)
⊥          ≔  ∀ p. p
¬ p        ≔  p ⇒ ⊥
p ∨ q      ≔  ∀ r. (p ⇒ r) ⇒ (q ⇒ r) ⇒ r
∃ P        ≔  ∀ q. (∀ x. P x ⇒ q) ⇒ q
ONE_ONE f  ≔  ∀ x y. f x = f y ⇒ x = y
ONTO f     ≔  ∀ y. ∃ x. y = f x
```

The kernel has no structural weakening.  `Derived.add_assum` recovers it
from `CONJ` + right projection, using a fresh name for the combinator
variable (HOL free variables are `(name, type)` pairs).

## Roadmap

### Phase 1 — Syntax, types, kernel (this slice)

- [x] Simple types + schematic instantiation
- [x] Locally nameless terms
- [x] Typing judgment, uniqueness, algorithmic inference
- [x] Type / term substitution lemmas
- [x] HOL Light kernel as `Provable`
- [x] Kernel theorems are closed booleans
- [x] Equality-only connectives and axiom schemas

### Phase 2 — Deeper metatheory (this slice, up through infinity)

- [x] Open/close cancellation (`open (close x t) = t` when `t` is closed;
      `close (open x t) = t` when `x` is fresh)
- [x] α-equivalence is identity on locally nameless terms
- [x] Derived rules: SYM, `|- T`, `EQT_INTRO`, GEN, general β via `INST`,
      CONJ, both projections, MP
- [x] Hypothesis weakening (`add_assum`) from CONJ + projection
- [x] `∃`, `¬`, `∨`, `ONE_ONE`, `ONTO` as `addDef` constants on `holLogic`
- [x] Infinity axiom: `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`
- [x] Environments: named constants with generic types; `holCore` / `holLogic` / `holEnv`; `addDef`
- [ ] Type definitional extensions (`new_basic_type_definition`) —
      **deferred** (see below)

### Environments vs definitional extensions

Infinity can be added in three different ways.  They are *not* interchangeable
once the object language, `INST` / `INST_TYPE`, and the eventual `ZFSet`
model are taken seriously.

| Approach | What changes | Language | Cost |
| --- | --- | --- | --- |
| **Named witness** (`indSuc : ind ↝ ind` + injectivity / non-surjectivity axioms) | Grow the constant table (an *environment*) | `{eq, select, indSuc}` | Every later lemma about terms, substitution, and the model must case-split on the new constant.  This is the same mechanism as `new_constant`. |
| **Existential axiom** (what we do) | Add one closed sentence | still `{eq, select}` plus defined connectives | The model only has to *satisfy* that `ω` is Dedekind-infinite (`succ` is a witness in the meta-theory).  No new primitive name. |
| **Definitional extension** (`new_basic_definition` / `new_basic_type_definition`) | Extend the signature by a constant *equal* to an existing closed term, or carve out a new type from a predicate | grows, but conservatively | Needs a conservation theorem relating *two* signatures, two environments, and two `INST`/`INST_TYPE` regimes.  Infinity has no closed witness term unless we already built one, so this does not replace the axiom. |

The environment is now explicit, so “add a constant” is `addConst` /
`addDef` and “add a sentence” is `addAxiom`.  Infinity stays existential:
a named `indSuc` would be a later `addConst` plus axioms, not a change of
kernel.  `addDef` installs `c = t` as an axiom (no δ).  Conservation of
definitional extensions, and type-level `new_basic_type_definition`, are
theorems *about* `Env.LE` — still ahead of the `ZFSet` model.

### Phase 3 — Standard model in `ZFSet`

Plan: [`docs/MODEL.md`](docs/MODEL.md).  Types, terms, kernel soundness,
`addDef` transport through `holLogic`, the `holEnv` axioms, and `¬ ⊢ ⊥`
are in.

Fix a type valuation `ρ : Name → ZFSet`.

| Object type | Interpretation |
| --- | --- |
| `var x` | `ρ x` |
| `bool` | `{∅, {∅}}` (`zfFalse` / `zfTrue`) |
| `ind` | `ZFSet.omega` |
| `α ↝ β` | `ZFSet.funs ⟦α⟧ρ ⟦β⟧ρ` |

- [x] Type denotation and `⟦α.inst θ⟧ ρ = ⟦α⟧ (ρ.inst θ)`
- [x] `zfBool`; graph application; `succ` injective / not surjective on `ω`
- [x] Term denotation (`HasType` → element of `⟦α⟧`)
- [x] `eq` / `select` as graphs; `EnvInterp.holCore`
- [x] soundness of the ten rules (`Provable.sound` / `sound_holCore`)
- [x] `addDef` preservation; model of `holLogic`
- [x] `holEnv` axioms; `⟦⊥⟧ = zfFalse`; `¬ [] ⊩[holEnv] ⊥`

**Soundness.**  If `Γ ⊩[env] p` and a valuation satisfies every hypothesis,
then `⟦p⟧ = zfTrue`.

**Consistency.**  `⟦⊥⟧ = zfFalse`, so `¬ ([] ⊩[holEnv] ⊥)`.  The same model
should satisfy η (functions *are* graphs), `SELECT` (`Classical.epsilon` /
`Class.choice`), and infinity (`succ : ω → ω`).

### Phase 4 — Lean frontend (this slice)

- [x] Reuse Lean's elaborator; translate `Lean.Expr` → `Ty` / `Tm`
- [x] Reject dependent types by the sort of the Π-body
- [x] `hol_ty(…)` / `hol_tm(…)` / `hol_prop(…)` / `hol(…)` / `#hol`

### Phase 5 — What we are *not* doing yet

- **Henkin completeness.**  Completeness needs general (Henkin) models,
  where `⟦α ↝ β⟧` may be a *subset* of the full function set.  Consistency
  only needs one sound model; the standard model is enough.
- **A verified checker / Candle-style kernel.**  `Provable` is a
  metatheoretic predicate, not an executable LCF kernel.  An executable
  `typeCheck` / `rule` layer can be added later and proved sound w.r.t.
  `Provable`.
- **Isabelle locales, HOL4 type operators, higher-rank polymorphism.**
  User type constructors (`Ty.app name args`) are the natural extension
  once the core model works — they become extra `ρ`-data in the signature.

## References

- A. Church, *A Formulation of the Simple Theory of Types*, JSL 1940
- A. M. Pitts, *The HOL Logic*, in the HOL4 documentation
- J. Harrison, HOL Light kernel (`fusion.ml`) and *Towards self-verification
  of HOL Light*
- R. Kumar, R. Arthan, M. O. Myreen, S. Owens, *Self-formalisation of higher-order
  logic* (Candle / CakeML)
- P. B. Andrews, *An Introduction to Mathematical Logic and Type Theory*
- Mathlib `SetTheory.ZFC.Basic` (`ZFSet`)
