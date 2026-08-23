# Standard model in `ZFSet`

This is the plan for interpreting HOLean in Mathlib's
[`ZFSet`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html).
The goal is a **standard** (full function-space) model, then soundness, then
`¬ ([] ⊩[holEnv] ⊥)`.

Henkin completeness, an executable LCF kernel, and type-level
`new_basic_type_definition` stay out of scope.

## Why this model

HOL Light's consistency is usually shown by a set-theoretic interpretation
(Harrison; Candle uses a similar story inside HOL itself).  We do it in Lean,
against the kernel we already have:

* schematic types, locally nameless terms, extrinsic `HasType env`
* environments `constants × axioms`, definitions as `⊢ c = t` (no δ)
* ten rules plus `Provable.ax`, connectives via `addDef` on `holLogic`

`ZFSet` already supplies the raw material: `funs` / `IsFunc` (graphs),
`omega`, Kuratowski `pair` / `prod`, `map`, and `Class.choice`.

## Target interpretation

Fix a type valuation `ρ : Name → ZFSet`.

| Object | Interpretation |
| --- | --- |
| `Ty.var x` | `ρ x` |
| `Ty.bool` | `{∅, {∅}}` (`zfFalse` / `zfTrue`) |
| `Ty.ind` | `ZFSet.omega` |
| `α ↝ β` | `ZFSet.funs ⟦α⟧ρ ⟦β⟧ρ` — *all* functional graphs |

This is the **standard** model: `⟦α ↝ β⟧` is the full function set, not a
Henkin subset.  η holds because every element of `funs` *is* a graph.

### Terms

Interpretation is defined by recursion on the raw term (`Tm.denote`),
because `HasType` is a `Prop` and cannot eliminate into `ZFSet`.
`HasType.denote_mem` then shows the result inhabits `⟦α⟧`:

```
Tm.denote     : EnvInterp env ρ → FVarVal ρ → List ZFSet → Tm → ZFSet
HasType.denote_mem : HasType env Γ t α → ⟦t⟧ ∈ ⟦α⟧
```

* `TyVal` — `Name → ZFSet`, the `ρ` above.
* `CtxVal Γ` — a list of sets, `vs[i] ∈ ⟦Γ[i]⟧`, for bound indices.
* `FVarVal` — a map `Name × Ty → ZFSet` with `ξ (x, α) ∈ ⟦α⟧`.
* `EnvInterp env ρ` — `I n inst ∈ ⟦inst⟧` whenever `inst` instantiates `env.constants n`.

Constructors:

| Term | Meaning |
| --- | --- |
| `bvar i` | `vs[i]` |
| `fvar x α` | `ξ (x, α)` |
| `const n inst` | `I n inst` (environment interpretation, below) |
| `app f a` | graph application `zfApp ⟦f⟧ ⟦a⟧` |
| `lam α t` | `ZFSet.map (fun x => ⟦t⟧ (x :: vs)) ⟦α⟧` |

Equality `s = t` at type `α` is the characteristic function of extensional
equality: `⟦eqConst α⟧` is the graph of `(x, y) ↦ if x = y then zfTrue else zfFalse`.

Hilbert `ε` at type `α` sends a predicate graph `P ∈ funs ⟦α⟧ zfBool` to some
`x ∈ ⟦α⟧` with `P x = zfTrue` if any such `x` exists, else an arbitrary
element of `⟦α⟧` (types of the standard model are nonempty: `bool`, `ind`,
and `funs` of nonempty sets).

### Environments

`HasType` reads only `constants`, so a model of an environment is a family

```
I : ∀ n inst, env.constants n = some gen → gen.isInstanceOf inst →
      { x // x ∈ ⟦inst⟧ }
```

that **satisfies every axiom**: if `env.axioms p` then `⟦p⟧ = zfTrue`
(under the empty context / any `ξ`).

Defined constants are not a second semantic layer.  `addDef n ty rhs`
extends `I` by `I n ty := ⟦rhs⟧`.  The new axiom `n = rhs` holds by
construction.  That is why connectives can stay `addDef` and still have a
model: interpret `holCore`, then transport along the `addDef` chain.

| Environment | What `I` must provide |
| --- | --- |
| `holCore` | `eq`, `select` |
| `holLogic` | those plus the connective constants, each equal to its RHS |
| `holEnv` | `holLogic` plus η, SELECT, INFINITY |

INFINITY stays an existential sentence.  The witness in the meta-theory is
`succ : ω → ω`, `n ↦ insert n n`.  We do **not** add an `indSuc` constant.

## Soundness and consistency

**Soundness.**  If `Γ ⊩[env] p`, `I` models `env`, and `ξ` makes every
hypothesis `zfTrue`, then `⟦p⟧ = zfTrue`.

The ten rules plus `ax` are the cases:

* `REFL` / `TRANS` / `MK_COMB` — graphs and extensional equality
* `ABS` — `x ∉ FV(Γ)` so the graph does not capture a hypothesis
* `BETA` — applying the graph of a λ is opening the body
* `ASSUME` — the hypothesis valuation already says `p` is true
* `EQ_MP` — `⟦p = q⟧ = zfTrue` means `⟦p⟧ = ⟦q⟧`
* `DEDUCT_ANTISYM` — each side is true exactly when the other is
* `INST_TYPE` — `⟦α.inst θ⟧ ρ = ⟦α⟧ (ρ.inst θ)` (type commutation)
* `INST` — substitution commutes with `denote`
* `ax` — `I` satisfies the axiom

**Consistency.**  `⟦falsum⟧ = zfFalse`, so `¬ ([] ⊩[holEnv] Tm.falsum)`.

η holds because `funs` contains only graphs.  SELECT uses Lean/`ZFSet`
choice on `{x ∈ ⟦α⟧ | P x = zfTrue}`.  INFINITY uses `succ` on `omega`.

## Mathlib pieces we actually use

From `Mathlib.SetTheory.ZFC.Basic` / `Class`:

* `ZFSet`, `∈`, `∅`, `insert`, `{x}`, `{x, y}`
* `pair`, `prod`, `IsFunc`, `funs`, `map`, `image`, `sep`
* `omega`, `omega_zero`, `omega_succ`
* `mem_asymm` / `mem_irrefl` (foundation — successor is injective)
* `Classical.allZFSetDefinable` when a `Definable₁` instance is tedious
* `Class.choice` / `Classical.epsilon` for `ε` and `ZFSet.app`

We do **not** need the ordinal/cardinal hierarchy for the first model.

## Module layout

```
HOLean/Model/Basic.lean   zfBool, zfTrue/zfFalse, graph application, succ
HOLean/Model/Ty.lean      Ty.denote, TyVal.inst, INST_TYPE commutation
HOLean/Model/Const.lean   I for eq / select (later: connectives)
HOLean/Model/Tm.lean      denote on raw terms; HasType.denote_mem
HOLean/Model/Commute.lean open / close / instTy / subst commute with denote
HOLean/Model/Sound.lean   EnvModel; Provable.sound; sound_holCore
HOLean/Model/Def.lean     addDef transport; EnvModel.holLogic
HOLean/Model/Axiom.lean   holEnv axioms; consistency
```

`Basic` through `Def` (including `holLogic` as a model) are in this PR.
The `holEnv` consistency argument is next.

## PR series (after this one)

Each slice should `lake build HOLean` and add theorems, not scaffolding alone.

1. **Terms** — `denote` for `HasType`, application/λ lemmas, `eq` as a graph.
2. **Kernel soundness** — the ten rules relative to any `I` that models `env`.
   `holCore` (no axioms) is the first instance.  **Done in this PR.**
3. **Definitions** — `addDef` preservation: if `I` models `env` and
   `HasType env [] rhs ty`, the extension models `env.addDef n ty rhs`.
   Then `holLogic` is a model.  **Done in this PR.**
4. **Axioms and consistency** — η, SELECT, INFINITY in `holEnv`;
   `⟦falsum⟧ = zfFalse`; `¬ [] ⊩[holEnv] ⊥`.

Type-level `new_basic_type_definition` remains deferred: it needs a
conservation theorem about two signatures, not just one model.
