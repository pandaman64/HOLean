# Verified forward reasoning (HOL Light in a Lean monad)

This is the design for a **new** LCF-style forward layer.  It is *not* a
refactor of `HolM` / `ProvTrace` / `Replay.buildProvable`.  Those remain
the current translation-validation path (`htheorem`).  This document
specifies a parallel path (`hdef'` / `htheorem'`) whose trust story is
**verified implementations**: the executable rules return kernel evidence
when they succeed, and a *minimal* elaborator only turns that evidence
into environment certificates.

Implementation follows this note; it has not started.

## Why a new layer

HOL Light’s kernel (`fusion.ml`) is a small ML API:

```ocaml
type thm                    (* abstract sequent *)
val REFL  : term -> thm
val TRANS : thm * thm -> thm   (* failwith on mismatch *)
```

OCaml gives two things Lean does not have for free:

1. **Exceptions** as the failure channel (`failwith "TRANS"`).
2. An **abstract `thm` type** so clients cannot forge sequents.

The current Lean analogue is `Elab.HolM`:

```
HolM α  ≔  ReaderT HolCtx (Except String) α
Hol.refl t : HolM CertifiedThm
CertifiedThm  ≔  { thm : Thm, trace : ProvTrace }
```

That monad *runs*, but it does not produce a `Provable` proof.  After a
script succeeds, `htheorem` **replays** the `ProvTrace` into a Lean term
(`Replay.buildProvable`, `elabHasType`).  Side conditions
(`env.lookup n = some gen`, `matchTy`, `freeIn x α = false`,
`tyvarsOk`, …) are discharged with per-node `rfl` / `decide`.  That is
**translation validation**: an untrusted implementation emits a
certificate; a second program reconstructs a kernel proof.

| | Translation validation (today) | Verified implementations (this design) |
| --- | --- | --- |
| Executable API | `HolM` + `ProvTrace` | `ProveM` + `CertifiedThm` |
| Evidence | derivation *trace* (data) | `HasType` / `Provable` *proofs* (return values) |
| Command | `hdef` / `htheorem` | `hdef'` / `htheorem'` |
| Elaborator | walks `Tm` / the trace, `mkApp*` of constructors, many `rfl` | quotes the user’s `ProveM` term, extracts with 1–3 definitional equalities |
| `DISCH` / `ASSUME` | not replayed into `_hol_prov` | ordinary kernel constructors |
| TCB | elaborator + kernel | `ProveM` functions + kernel (elaborator is not in the TCB) |

The existing lemmas we reuse rather than re-prove:

* `HasType.of_infer` / `HasType.iff_infer` (`Typing.lean`)
* every `Provable.*` constructor (`Deduction.lean`)
* derived rules `Provable.eq_sym`, `gen`, `spec`, `tru_intro`, … (`Derived.lean`)
* `Env.WF.addDef` / `addAxiom` (`Typing.lean`, `Elab/Cert.lean`)

We do **not** use `native_decide` / `ofReduceBool` (dropped from the TCB
in `de9eff5`).

## Goals

1. A Lean monad that feels like HOL Light: `do`-notation, `failwith`-style
   errors, combinators `refl`, `trans`, `mkComb`, …
2. Successful computations **return proofs**, e.g.
   `checkType tm ty : ProveM env (Proof (HasType env Γ tm ty))`.
3. `CertifiedThm env` packages a sequent with a real `Provable env hyps concl`.
4. `hdef'` / `htheorem'` are a thin command layer: translate surface syntax
   with the existing `hol_tm` / telescope elaborator, then apply generic
   extractors.  No `elabHasType`, no `buildProvable`, no `proveByRfl` loops.
5. Each successful command **registers an updated `Env`**.  The next
   `hdef'` / `htheorem'` builds `ProveCtx` for that env and evaluates the
   monad there.  Proved theorems live in `env.axioms` (via `addAxiom`);
   definitions live in the constant table plus a defining axiom
   (`addDef`).  A **name roster** in the registered state (`HolDecl`)
   maps HOL names to those sentences so `Hol.thm` can look them up; it
   is not a store of `CertifiedThm` proofs.
6. Closed scripts emit the same *kind* of certificates as today
   (`_hol_wf`, `_hol_prov`, model / consistency when the sequent is closed),
   but the `_hol_prov` term is an application of the verified API, not a
   reconstructed constructor tree for `HasType`.

## Non-goals (this slice)

* Replacing `hdef` / `htheorem` / `hby`.  They keep working.
* Replaying `ProvTrace`.  New scripts do not allocate traces.
* InfoView Goals (`docs/INFOVIEW.md`).
* Type-level `new_basic_type_definition`.
* A CakeML/Candle-style *external* checker.  Evidence lives in Lean’s
  kernel, produced by Lean functions we prove correct *by construction*.

## Architecture

```
  current env  ──►  ProveCtx env  ──►  ProveM script
                                              │
                         extract (isOk)       ▼
                                    CertifiedThm / DefWitness
                                              │
                         hdef' / htheorem'    ▼
                         env' ≔ env.addDef / addAxiom
                         persist HolDecl (env' + name roster) + HolCert
                                              │
                                              ▼
                                    next command’s ProveM
                                    runs against env'
```

The deduction predicate `Provable` stays the spec.  `ProveM` is an
implementation of that spec, in the same sense that `Tm.infer` is an
implementation of `HasType`.

## The monad (OCaml → Lean)

| HOL Light (OCaml) | Lean |
| --- | --- |
| `failwith msg` | `ProveM.throw msg` (`Except String`) |
| global `the_term_constants` / axioms | `ProveCtx env` (frozen for one script) |
| `new_basic_definition` (command) | `hdef'` (grows `Env` between commands) |
| abstract `thm` | `CertifiedThm env` (constructor not part of the user API) |
| `try … with Failure → …` | `orElse` / `tryCatch` on `Except` |

### Context

A script is typed in a **fixed** environment.  Mutation is a command
concern, matching HOL Light’s split between `fusion.ml` (pure inference)
and `bool.ml` / `equal.ml` (theory packaging).  The command layer is the
only writer; the monad is a reader of the env that command just passed in.

```lean
structure ProveCtx (env : Env) where
  wf    : env.WF
  hasEq : Env.HasEq env
  conn  : Env.HasConnectives env
  /-- Name roster from registered `HolDecl`s: HOL name → axiom sentence.
  Evidence is still `p ∈ env.axioms`, not a stored proof. -/
  thms  : List (Name × Tm)
```

`HasConnectives` is required so derived rules (`truth`, `spec`, `gen`,
`disch`) can use the lemmas in `Derived.lean` without a separate instance
search inside the monad.  Primitive equality-only rules only need `hasEq`.

Previous declarations are **already in `env`**, which is how `Env` is
defined today (`constants` × `axioms`):

* `hdef' c : τ := rhs` registers `env.addDef c τ rhs` — `c` becomes
  `lookup`-able and `⊢ c = rhs` is an axiom.  `HolDecl.defn` records
  `(c, τ, rhs)` so `Hol.defn` can recover the defining equation.
* `htheorem' n : p := …` registers `env.addAxiom p` — `p` is in
  `env.axioms`.  `HolDecl.thm` records `(n, p)` so `Hol.thm n` can find
  `p` by name.

The next command folds `holStateExt` onto `holEnv` (same `HolDecl.apply`
as today), copies the name roster into `ProveCtx.thms`, and evaluates
`ProveM` against **that** env.

`Hol.thm n` is a monad operation, not elaborator sugar:

1. look up `n` in the roster → sentence `p`;
2. `checkMemAxioms p` (`p ∈ env.axioms`);
3. `CertifiedThm` via `Provable.of_axiom ctx.wf`.

A stale or forged roster entry that does not match `env.axioms` fails
at step 2.  The roster never carries a previous script’s proof tree.

## Growing the environment

`ProveM` never calls `addDef` / `addAxiom`.  The commands do, then hand
the extension to the next evaluation:

```
env₀ = holEnv

hdef' / htheorem' ₁
  ctx₀ ← ProveCtx for env₀          -- wf / conn from HolCert.holEnv
  run script in ProveM env₀
  env₁ ← env₀.addDef …  or  env₀.addAxiom …
  persist HolDecl; set HolCert for env₁

hdef' / htheorem' ₂
  ctx₁ ← ProveCtx for env₁          -- wf / conn from the previous HolCert
  run script in ProveM env₁         -- infer, ax, defn see env₁
  env₂ ← …
```

So `htheorem' true_eq_true_again : True = True := Hol.thm "true_eq_true_fwd"`
looks up `"true_eq_true_fwd"` in the roster, checks that sentence is in
`env₁.axioms`, and applies `ax`.

`CertifiedThm env` is **intra-script** evidence (composing
`REFL`/`TRANS`/… in one `do` block).  Crossing a command boundary goes
through `Env` (and the name roster).  We do not wrap old `CertifiedThm`s
into `ProveCtx`.

### `ProveM`

`Except` is restricted to `Type`, so a result in `Prop` must be lifted.
We use a one-field wrapper rather than a custom `Sort u` `Except`:

```lean
/-- Kernel evidence as a `Type` so `Except` / `do` work. -/
abbrev Proof (p : Prop) := PLift p

abbrev ProveM (env : Env) : Type u → Type u :=
  ReaderT (ProveCtx env) (Except String)
```

`Proof (HasType env Γ tm ty)` is what the informal signature
`ProveM (HasType gamma tm ty)` meant: the proof is present **only** on
the `ok` path.

Helpers:

```lean
def ProveM.run {env α} (x : ProveM env α) (ctx : ProveCtx env) :
    Except String α :=
  ReaderT.run x ctx

def ProveM.throw {env α} (msg : String) : ProveM env α :=
  fun _ => .error msg

def ProveM.okProof {env} {p : Prop} (h : p) : ProveM env (Proof p) :=
  pure ⟨h⟩
```

Failure messages stay human-readable (`"TRANS: conclusions do not join"`),
like HOL Light.

## Certified sequents

```lean
structure CertifiedThm (env : Env) where
  hyps  : List Tm
  concl : Tm
  proof : Provable env hyps concl
```

This is the LCF invariant: a value of this type *is* a deduction.  The
module `HOLean.Prove.Kernel` is the only place that builds the structure
(plus derived wrappers that go through those functions).  User files
never write `CertifiedThm.mk`.

There is **no** `ProvTrace`.  Composition *is* composition of `Provable`
constructors.

`Thm` (the untrusted sequent in `Elab/Kernel.lean`) is not reused.  The
old `CertifiedThm` name in `HOLean.Elab` stays there; the new type lives
in `HOLean.Prove` and should be referred to as `Prove.CertifiedThm` if
both are in scope.

## Type checking as a verified implementation

Algorithmic inference already exists (`Tm.infer`) and is complete for
`HasType`.  The new API **returns the judgment**:

```lean
variable {env : Env}

/-- Infer `tm`’s type, or fail. -/
def infer (Γ : List Ty) (tm : Tm) :
    ProveM env (Σ ty : Ty, Proof (HasType env Γ tm ty)) := do
  match h : tm.infer env Γ with
  | some ty => return ⟨ty, ⟨HasType.of_infer h⟩⟩
  | none    => ProveM.throw s!"not well-typed: {repr tm}"

/-- Check `tm` against an expected type. -/
def checkType (Γ : List Ty) (tm : Tm) (ty : Ty) :
    ProveM env (Proof (HasType env Γ tm ty)) := do
  let ⟨ty', ht⟩ ← infer Γ tm
  if h : ty' = ty then
    return ⟨h ▸ ht.down⟩
  else
    ProveM.throw s!"expected type {repr ty}, got {repr ty'}"
```

The dependent `match h : tm.infer env Γ` is the entire trust step for
typing.  `h` *is* `tm.infer env Γ = some ty`; `HasType.of_infer h` is a
single lemma.  The elaborator does not emit `HasType.const (rfl : lookup
= _) (rfl : instantiates _)` for each constant occurrence.

Same pattern for other Boolean side conditions:

```lean
def checkFreshHyps (x : Name) (α : Ty) (Γ : List Tm) :
    ProveM env (Proof (∀ p ∈ Γ, p.freeIn x α = false))

def checkSubst (σ : Tm.Subst) :
    ProveM env (Proof (σ.Ok env))

def checkFreshConst (n : Name) :
    ProveM env (Proof (env.lookup n = none))

def checkMemAxioms (p : Tm) :
    ProveM env (Proof (p ∈ env.axioms))

def checkClosed (t : Tm) :
    ProveM env (Proof (t.LC 0 = true))

def checkBool (Γ : List Ty) (t : Tm) :
    ProveM env (Proof (HasType env Γ t .bool)) :=
  checkType Γ t .bool
```

`if h : a = b` / `match h : t.freeIn x α with` use `DecidableEq` and
Boolean recursor proofs.  Those equalities are *hypotheses of the
branch*, not elaborator-synthesized `rfl` terms.

## Kernel rules

Each HOL Light primitive is a `ProveM` function that:

1. destructs conclusions (`Tm.destEq`, …);
2. checks side conditions through the helpers above;
3. returns a `CertifiedThm` whose `proof` field is the corresponding
   `Provable` constructor.

Sketch of `REFL` (the user’s `refl : Tm → ProveM CertifiedThm`):

```lean
def refl (tm : Tm) : ProveM env (CertifiedThm env) := do
  let ⟨α, ht⟩ ← infer [] tm
  return {
    hyps  := []
    concl := Tm.mkEq α tm tm
    proof := Provable.refl ht.down
  }
```

`TRANS` (failure is an exception, success is `Provable.trans`):

```lean
def trans (th1 th2 : CertifiedThm env) : ProveM env (CertifiedThm env) := do
  match Tm.destEq th1.concl, Tm.destEq th2.concl with
  | some (α, s, t), some (β, t', u) =>
    if hα : α = β then
      if ht : t = t' then
        return {
          hyps  := th1.hyps ++ th2.hyps
          concl := Tm.mkEq α s u
          proof := hα ▸ ht ▸ Provable.trans th1.proof th2.proof
        }
      else ProveM.throw "TRANS: conclusions do not join"
    else ProveM.throw "TRANS: type mismatch"
  | _, _ => ProveM.throw "TRANS: expected equations"
```

The other primitives follow the same shape as `Elab.Hol.*` *control
flow*, but the return type carries `Provable`:

| Function | Side conditions via | Proof |
| --- | --- | --- |
| `refl t` | `infer [] t` | `Provable.refl` |
| `trans th₁ th₂` | `destEq` + `= ` | `Provable.trans` |
| `mkComb th₁ th₂` | `destEq` on `α ↝ β` | `Provable.mkComb` |
| `abs x α th` | `checkFreshHyps` + `destEq` | `Provable.abs` |
| `beta x α t` | `infer [α] t` | `Provable.beta` |
| `assume p` | `checkBool [] p` | `Provable.assume` |
| `eqMp th₁ th₂` | `destEq` at `bool` | `Provable.eqMp` |
| `deductAntisym th₁ th₂` | none | `Provable.deductAntisym` |
| `instType θ th` | none | `Provable.instType` |
| `inst σ th` | `checkSubst σ` | `Provable.inst` |
| `ax p` | `checkMemAxioms p` | `Provable.of_axiom ctx.wf` |

`ax` is how a sentence **already in `env.axioms`** becomes a
`CertifiedThm`.  Named recall is `thm`, which uses the roster then `ax`:

```lean
def ax (p : Tm) : ProveM env (CertifiedThm env) := do
  let ctx ← read
  let ⟨hp⟩ ← checkMemAxioms p
  return { hyps := [], concl := p, proof := Provable.of_axiom ctx.wf hp }

def thm (n : Name) : ProveM env (CertifiedThm env) := do
  match (← read).thms.find? (fun e => e.1 == n) with
  | none => ProveM.throw s!"no theorem `{n}`"
  | some (_, p) => ax p
```

`defn n` recovers `c = rhs` from the registered definition (or a
built-in table) and likewise calls `ax`, so the defining equation must
be in `env.axioms`.  Built-in `holEnv` sentences (η, SELECT, INFINITY,
connective definitions) are already in `holEnv.axioms`; they do not
need roster entries unless we want `Hol.thm` to name them.

### Derived rules

These call the primitives (or `Provable` lemmas already proved in
`Derived.lean`) so we do not expand a long equality-based derivation at
the elaborator:

* `sym`, `truth`, `disch`, `gen`, `spec`
* `eta`, `select`, `infinity` (instantiate closed axioms already in `holEnv`)
* `defn n` — name → defining equation, then `ax` (must be in `env.axioms`)
* `ax p` — any `p ∈ env.axioms`
* `thm n` — roster lookup, then `ax`

`DISCH` / `ASSUME` are first-class.  Closed `htheorem'` scripts that
discharge telescope hypotheses can still emit `_hol_prov`, which the
replay path currently cannot.

## Definition certificates (for `hdef'`)

Pack every `addDef` side condition into one computation:

```lean
structure DefWitness (env : Env) (n : Name) (ty : Ty) (rhs : Tm) where
  fresh  : env.lookup n = none
  typed  : HasType env [] rhs ty
  closed : rhs.LC 0 = true
  tyvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars
  names  : nameNotInConnectiveAndPrim n

def certifyDef (n : Name) (ty : Ty) (rhs : Tm) :
    ProveM env (Proof (Nonempty (DefWitness env n ty rhs)))
```

(Alternatively return `DefWitness` itself, since it is already in `Type`.)
`Env.WF.addDef` and `EnvModel.addDef` consume these fields directly.
The command elaborator never proves `lookup = none` by `rfl` on a
concrete association list.

## Minimal elaborator

Surface syntax stays.  Only the *evidence path* changes.

### Shared with today

* `hol_ty` / `hol_tm` / `hol_prop` / `⌜·⌝` (`Elab/Term.lean`)
* left-hand telescopes (`Elab.HolTelescope`)
* `holStateExt` for the cumulative user environment
* certificate *lemmas* in `Elab/Cert.lean` (`cert_wf_addDef`, …)

### Not used by `hdef'` / `htheorem'`

* `unsafe evalHolMCertified`
* `ProvTrace`, `Replay.elabHasType`, `Replay.buildProvable`
* `proveByRfl`, `proveNotFree`, `mkInstantiatesProof`, `mkListGetElem?`
* `evalExpr` of a `CertifiedThm` (Prop fields would be erased; we never
  round-trip proofs through the VM)

### `htheorem'`

1. Elaborate binders + statement to `HolTelescope` (existing).
2. Elaborate the proof term as `ProveM env (CertifiedThm env)`
   (**kernel-visible Lean term**, not `evalExpr`).
3. Wrap with a generic closer:

   ```lean
   def closeTheorem (tel : HolTelescope) (m : ProveM env (CertifiedThm env)) :
       ProveM env (Proof (Provable env [] tel.stmt))
   ```

   This runs `m`, then `disch` / `gen` for telescope binders (the same
   order as `closeThmWithTelescope`), then checks `hyps = []` and
   `concl = tel.stmt` with `if h :`.

4. Add a definition `name_script : ProveM env (CertifiedThm env)` (or
   the closed `ProveM env (Proof (Provable …))`), where `env` is the
   **current** cumulative environment (`envExprFromDecls`).
5. Extract a `Provable env [] stmt` proof with the generic lemma below.
6. Register `HolDecl.thm` so the persistent env becomes
   `env.addAxiom stmt`.  Emit `_hol_wf` / `_hol_prov` / model
   certificates by `mkAppN` of `cert_*` lemmas.  The next command’s
   `ProveM` is parameterized by this `env.addAxiom stmt`.

VM evaluation (`Meta.evalExpr`) is allowed **only** to print a failure
string when `run` is `.error`.  It is not a source of kernel evidence.

### `hdef'`

1. Elaborate binders + RHS as today (`exprToTyVal` / `exprToTmVal`).
2. The evidence term is `certifyDef holN ty rhs`.
3. Extract `DefWitness`, apply `cert_wf_addDef` / `cert_model_addDef`.
4. Register `HolDecl.defn` so the persistent env becomes
   `env.addDef holN ty rhs`.  Lean placeholder definition as today.
   The next command’s `ProveM` is parameterized by this `env.addDef …`
   (the new constant is `lookup`-able; `⊢ c = rhs` is in `axioms`).

### Extraction without a `rfl` storm

`ProveM.run script ctx` has type `Except String α`.  Certificates need
the `ok` payload.  We prove **once**:

```lean
def Except.getOk {ε α} : (r : Except ε α) → r.isOk = true → α

theorem ProveM.extractProvable {env} (ctx : ProveCtx env) (stmt : Tm)
    (m : ProveM env (Proof (Provable env [] stmt)))
    (hok : (m.run ctx).isOk = true) :
    Provable env [] stmt :=
  ((m.run ctx).getOk hok).down
```

`hdef'` analogously extracts a `DefWitness`.

At each command the elaborator must still produce `hok` (and, if the
wrapper does not already pin `concl`, equalities `hyps = []` /
`concl = stmt`).  That is **one Bool/List/Tm equality per command**,
proved by kernel reduction of `run` (`rfl` after `isOk` reduces to
`true`).  It is *not* one `rfl` per `lookup` / `matchTy` / `getElem?`.

What the kernel reduces is the **control flow** of the script (`destEq`
branches, `infer` on the terms that `REFL`/`BETA`/`ASSUME` actually
type-check).  `HasType` evidence stays as `HasType.of_infer h`; we do
not unfold it into a constructor tree.

`_hol_prov` is therefore a small term:

```lean
theorem name_hol_prov : [] ⊩[env] stmt :=
  ProveM.extractProvable ctx stmt name_script ⟨rfl⟩
```

`EnvModel.addAxiom` takes that theorem.  Unfolding `name_script` is not
required to *store* the certificate; type-checking `rfl` is the only
global reduction.

If a later script is too large for a single kernel `rfl` on `isOk`, the
fallback is still *not* replay: split the script into named
`CertifiedThm` lemmas (each with its own one-line extract), the same
way HOL Light factors `prove` calls.  We will not reintroduce
`native_decide`.

### `ProveCtx` at the command boundary

The elaborator builds a `ProveCtx env` *term* for the env **as of this
command** (previous decls already applied):

* `env` — `envExprFromDecls` (already in `Cert.lean`)
* `wf` / `hasEq` / `conn` — previous `HolCert` constants (`_hol_wf`,
  `_hol_conn`, … of the last `hdef'` / `htheorem'`, or `holEnv`’s)
* `thms` — name roster from `holStateExt` (`HolDecl.thm` → `(n, stmt)`).
  Same persistent array the command already writes; copied into
  `ProveCtx` so `Hol.thm` is ordinary `ProveM` code.

After a successful command, `addHolDecl` extends the roster and
`setHolCert` points at the new env’s WF / connectives / model.  The
next `ProveCtx` is those certificate projections plus the new `env`
and the extended roster.

No `rfl` is needed to *construct* `ctx`; it is `mkAppN` of existing
certificate names plus `toExpr` of the roster.

## User-facing shape

Scripts look like today’s `Examples/Forward.lean`, with `ProveM` instead
of `HolM`:

```lean
htheorem' true_eq_true_fwd : True = True :=
  Hol.refl (hol_tm(True))
-- registers env₁ = env₀.addAxiom (True = True)

htheorem' true_eq_true_again : True = True :=
  Hol.thm "true_eq_true_fwd"
-- roster → p; check p ∈ env₁.axioms; CertifiedThm via ax

htheorem' true_via_eqmp : True := do
  let heq ← Hol.sym (← Hol.defn "tru")
  let hr  ← Hol.refl (hol_tm(fun (p : Prop) => p))
  Hol.eqMp heq hr

hdef' myId {A : Type} (x : A) := x
-- registers env.addDef myId …; later scripts infer/check against that constant
```

`Hol.defn "tru"` works in the first script already, because `tru`’s
defining axiom is in `holEnv.axioms` before any user command.

`do`-notation is Lean’s, standing in for OCaml sequencing.  Binders on
`htheorem'` still mean `GEN` / `DISCH` at the closer, not inside the
user’s script, unless the script does that explicitly.

## Module layout

New files; nothing in `Deduction.lean` / `Typing.lean` needs to change
for the first slice.

```
HOLean/Prove/Basic.lean      ProveCtx, Proof, ProveM, CertifiedThm, extract
HOLean/Prove/Typecheck.lean  infer, checkType, checkFreshHyps, checkMemAxioms, …
HOLean/Prove/Kernel.lean     ten primitives + ax / defn / thm
HOLean/Prove/Derived.lean    sym, truth, disch, gen, spec, eta, select, infinity
HOLean/Prove/Def.lean        DefWitness, certifyDef
HOLean/Prove.lean            barrel
HOLean/Elab/ProveDecl.lean   hdef' / htheorem' / closeTheorem
Examples/ProveForward.lean   ports of Examples/Forward.lean
docs/FORWARD.md              this file
```

`HOLean/Prove/*` must **not** import `Lean.Elab`.  They may import
`Deduction`, `Derived`, `Axiom`, `Connective`.  That keeps the verified
API usable in proofs that never load the frontend (the model already
depends on `Provable`, not on `HolM`).

Namespace: `HOLean.Prove` for the monad and `HOLean.Prove.Hol` for the
rule names (`refl`, `trans`, …), so `open Hol` in an `htheorem'` script
matches HOL Light’s `REFL`/`TRANS` vocabulary (Lean-case).

## Trust boundary

```
                    ┌─────────────────────────────────┐
  user script       │ ProveM term  (Lean, checked)    │
                    └──────────────┬──────────────────┘
                                   │ extract (1× isOk)
                    ┌──────────────▼──────────────────┐
  kernel            │ Provable / HasType / Env.WF     │
                    └──────────────┬──────────────────┘
                                   │ already proved
                    ┌──────────────▼──────────────────┐
  model             │ EnvModel, ¬ ⊢ ⊥                 │
                    └─────────────────────────────────┘
```

The command elaborator is outside the box: a bug there can fail to
install a declaration or can install a *weaker* certificate, but it
cannot manufacture a `Provable` that did not come from `ProveM`.  That
is the opposite of `Replay.buildProvable`, whose correctness is not
proved — we only type-check the term it happens to build.

## Relation to `hby`

Tactic mode can later be retargeted: `HolTacM` would thread
`CertifiedThm` / open `ProveM` goals instead of `ProvTrace` holes.
That is a separate slice.  Until then, `hby` stays on the old path.

## Implementation order

Work proceeds in this order so each step is independently checkable:

1. `Prove/Basic.lean` + `Typecheck.lean` (`infer` / `checkType` only),
   with a few `#eval` / example theorems that `checkType` succeeds on
   `hol_tm(True)` in `holEnv`.
2. `Prove/Kernel.lean` — ten rules; unit tests as `ProveM` scripts
   reduced with `rfl` on `isOk` (no elaborator yet).
3. `Prove/Derived.lean` + `Def.lean`.
4. `Elab/ProveDecl.lean` — `htheorem'` for closed `Hol.refl` /
   `Hol.trans` scripts; persist `addAxiom` and pass the new env into
   the next command; emit `_hol_prov` via `extractProvable`.
5. `hdef'` + WF / model certificates from `DefWitness`; persist
   `addDef` so later `ProveM` sees the constant.
6. Port `Examples/Forward.lean` to `Examples/ProveForward.lean`,
   including `Hol.thm` via roster lookup + `ax`.
7. Telescope `DISCH`/`GEN` in `closeTheorem`.

Do not delete `HolM` until this path covers the Forward examples and
the certificate surface (`#hol_cert`) looks the same.

## Design choices worth not reopening

* **Proofs as return values, not a soundness axiom.**  An opaque `thm`
  plus `axiom sound : …` would mimic HOL Light’s abstract type but would
  add axioms.  `CertifiedThm.proof` is definitional.
* **`PLift` / `Proof`, not a `Sort u` monad.**  `do`-notation and
  `Except` stay standard.
* **`ReaderT` over a frozen `env`, not `StateT Env`.**  Inference does
  not allocate constants; `hdef'` / `htheorem'` do, at command
  granularity, and pass the extension into the next `ProveM`.
* **Roster is names, not proofs.**  Registered `HolDecl` / `ProveCtx.thms`
  map `Name` to an axiom sentence.  `Hol.thm` looks that up, checks
  `p ∈ env.axioms`, then `Provable.of_axiom`.  We do not store
  `CertifiedThm` in the side table.
* **Keep `Provable` inductive.**  We are not switching to a verified
  *checker* of traces.  Traces were the translation-validation artefact.
* **One extract `rfl` per command is in budget.**  Per-node `rfl` in
  `elabHasType` is what we are leaving.
