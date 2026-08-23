# HOLean

A Lean 4 formalization of **Higher-Order Logic** — Church's Simple Type Theory
with schematic (ML-style) polymorphism — in the style of the HOL Light kernel.
The long-term goal is a **set-theoretic consistency proof**: interpret the
object logic in Mathlib's [`ZFSet`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html)
and conclude `⊬ ⊥`.

This repository currently defines the syntax, the type theory, and the
inference system, and proves the first layer of formal metatheory (unique
typing, substitution lemmas, and that every kernel theorem is a closed
boolean).

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
  Syntax/Ty.lean       simple types, type substitution
  Syntax/Const.lean    primitive constants `eq`, `select` (no `indSuc`)
  Syntax/Tm.lean       locally nameless terms, shift / LC / open–close
  Typing.lean          `HasType`, inference, substitution lemmas
  Connective.lean      T, ∧, ⇒, ∀, ⊥, ¬, ∨, ∃, ONE_ONE, ONTO
  Kernel.lean          ten HOL Light rules (`Provable`)
  Derived.lean         SYM, GEN, CONJ, projections, MP, weakening
  Axiom.lean           η / SELECT / INFINITY schemas; `Proves`
```

Mathlib is already a dependency so the later model can use `ZFSet.funs`,
`ZFSet.omega`, and `ZFSet.choice`.  The files above do not import it.

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

### Lists as hypothesis sets

`Provable` stores hypotheses as `List Tm`.  The rules use `++` and
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
hypotheses and a closed boolean conclusion.

Defined connectives are **Lean term formers**, not object-language constants
(see “Environments vs definitional extensions” below).  Arguments placed
under a binder are `shift`ed, so the formers are capture-avoiding on open
terms:

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
- [x] `∃`, `¬`, `∨`, `ONE_ONE`, `ONTO` as defined terms
- [x] Infinity axiom: `∃ f : ind ↝ ind. ONE_ONE f ∧ ¬ ONTO f`
- [ ] Definitional extensions (`new_basic_definition`,
      `new_basic_type_definition`) — **deferred** (see below)

### Environments vs definitional extensions

Infinity can be added in three different ways.  They are *not* interchangeable
once the object language, `INST` / `INST_TYPE`, and the eventual `ZFSet`
model are taken seriously.

| Approach | What changes | Language | Cost |
| --- | --- | --- | --- |
| **Named witness** (`indSuc : ind ↝ ind` + injectivity / non-surjectivity axioms) | Grow the constant table (an *environment*) | `{eq, select, indSuc}` | Every later lemma about terms, substitution, and the model must case-split on the new constant.  This is the same mechanism as `new_constant`. |
| **Existential axiom** (what we do) | Add one closed sentence | still `{eq, select}` | The model only has to *satisfy* that `ω` is Dedekind-infinite (`succ` is a witness in the meta-theory).  No new object-level name. |
| **Definitional extension** (`new_basic_definition` / `new_basic_type_definition`) | Extend the signature by a constant *equal* to an existing closed term, or carve out a new type from a predicate | grows, but conservatively | Needs a conservation theorem relating *two* signatures, two environments, and two `INST`/`INST_TYPE` regimes.  Infinity has no closed witness term unless we already built one, so this does not replace the axiom. |

We take the existential form so Phase 3 can interpret a **fixed** two-constant
language.  An environment (map from constants to types, later to denotations)
is the right place to host `indSuc` *or* defined constants — but then
`HasType`, `Provable`, and the model all become relative to that map.
`new_basic_definition` is a *theorem about* such extensions (the new constant
is conservative).  Mixing “add a constant” with “prove conservation” before
the environment is explicit makes the two mechanisms hard to compare.

That is why definitional extension is *not* in this slice: the tradeoff is
exactly whether infinity (and later definitions) should grow an environment
or stay as sentences in a fixed language.  We want that choice visible
before encoding `new_basic_definition`.

### Phase 3 — Standard model in `ZFSet`

Fix a type valuation `ρ : Name → ZFSet`.

| Object type | Interpretation |
| --- | --- |
| `var x` | `ρ x` |
| `bool` | `{∅, {∅}}` (or any two-element set) |
| `ind` | `ZFSet.omega` |
| `α ↝ β` | `(⟦α⟧ ρ).funs (⟦β⟧ ρ)` |

Mathlib already provides the pieces:

- `ZFSet.funs x y` — the set of functional graphs `x → y` (`IsFunc`)
- `ZFSet.omega` — von Neumann ω
- `ZFSet.choice` — for `SELECT`
- `ZFSet.powerset`, `ZFSet.prod`, `ZFSet.pair`

Term interpretation (for `HasType Γ t α`) is a function

```
⟦Γ⟧ρ → (Name × Ty → ZFSet) → ⟦α⟧ρ
```

that sends λ to the graph of a function (`ZFSet.map` / comprehension into
`funs`) and `=` to the characteristic function of extensional equality.

**Soundness.**  If `Γ ⊩ p` and a valuation satisfies every hypothesis, then
`⟦p⟧ = true`.

**Consistency.**  `⟦⊥⟧ = false`, so `¬ ([] ⊩ ⊥)`.  With axioms, the same
model should satisfy η (functions *are* graphs), `SELECT` (via
`ZFSet.choice` or a definable well-order on the well-founded universe), and
infinity (`succ : ω → ω` is injective and not surjective).

### Phase 4 — What we are *not* doing yet

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
