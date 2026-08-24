# InfoView for HOL tactics (design note)

This is a **reference for a later InfoView integration**, not a current
implementation plan.  `hby` already reports remaining sequents as Lean
*messages*.  The Goals panel, hover, and click-to-jump are a different
channel.

The two mature examples in the Lean ecosystem are:

* **mvcgen / `Std.Do` proof mode** (Lean 4 core)
* **iris-lean proof mode** (`leanprover-community/iris-lean`)

They do *not* ship a custom Goals panel.  They stay in ordinary Lean
tactic mode and change **how the current goal type is pretty-printed**.
ProofWidgets is a heavier, orthogonal option (a React panel next to
Goals).  Both are sketched below, then mapped onto HOLean.

## What InfoView actually shows

Lean's InfoView has several independent feeds.  Mixing them up is the
usual reason “custom goals” fail to appear.

| Feed | What it is | Typical API | Where it shows |
| --- | --- | --- | --- |
| **Goals** | Pretty-printed types of unsolved `MVarId`s, plus the local context, recorded in `TacticInfo` | `withTacticInfoContext`, elaborating a real tactic / term mvar | Goals panel |
| **Expected type** | The type expected at the cursor in a term | term elaborator | Term goal |
| **Messages** | `logInfo` / `logInfoAt` / `throwError` | `CommandElabM` / `MetaM` | Messages (and squiggles) |
| **Widgets** | React components loaded from `@[widget_module]` | `Widget.savePanelWidgetInfo`, ProofWidgets | Extra panel(s) |

The Goals panel does **not** watch `logInfoAt`.  It watches **metavariables
in `TacticInfo`**, then delaborates their types.  A `CommandElab` that
never opens a Lean mvar therefore cannot appear in Goals, no matter how
carefully it formats the sequent.

User widgets also cannot be *embedded inside* the standard goal view
(lean4#1225).  A widget is an extra panel, or a presentation of a
particular `Expr`, not a replacement of the Goals renderer.

## Current HOLean

`htheorem … := hby tacs` is a **command elaborator**.  The tactic state
(`HolTacState`: remaining sequents + `ProvTrace`) lives in Lean
metaprogramming state, not as Lean goals.

Unsolved `hby` currently:

1. `logInfoAt` the sequents (before/after each tactic, and on failure)
2. `throwErrorAt` `HOLean: unsolved goals` at the `hby` token / tactic
   block

That is the Messages path.  It is enough for `#guard_msgs` tests and for
a text dump of `Γ ⊢ P`.  It is **not** InfoView Goals:

* no clickable hypotheses
* no per-tactic goal snapshot as you move the cursor through the script
* `hbegin` / `htac` / `#hol_goals` are a second command-level session
  (not persisted in `.olean`)

The LCF proof (`ProvTrace` → `Replay.buildProvable`) is independent of
display.  Any InfoView work should keep that split: **pretty-print a
view of the sequent; do not re-prove it in Lean**.

## Approach A — proof-mode delaborator (mvcgen, iris-lean)

This is the cheap, well-tested way to get a “custom” Goals experience.

### Idea

1. Elaborate `hby` (or `istart` / `mstart`) as a **Lean tactic** on a
   real `MVarId` whose type is a `Prop`.
2. Encode the domain-specific context **inside that goal type**, not as
   Lean locals.
3. Use a **marker constant** that is definitionally the real entailment,
   so a delaborator can recognize “we are in proof mode”.
4. Pretty-print the marker as multi-line “hypothesis / turnstile / goal”
   syntax.  InfoView just shows that string.

No JavaScript, no extra panel, no change to vscode-lean.  Cursor motion
through the tactic script works because Lean already records
`TacticInfo` at each tactic.

### Marker constant

mvcgen (`Std.Tactic.Do.ProofMode`):

```lean
abbrev MGoalEntails := @SPred.entails
def MGoalHypMarker {σs : List (Type u)} (_A : SPred σs) : Prop := True
```

iris-lean (`Iris.ProofMode`):

```lean
def Entails' [BI PROP] : PROP → PROP → Prop := Entails
```

The marker is *not* the user-facing notation (`⊢ₛ`, `⊢`).  It exists so
that:

* `parseMGoal?` / `parseIrisGoal?` can detect proof mode by head symbol
* a `@[delab app.…]` (or `@[builtin_delab]`) fires only on that head
* `rw` / `simp` on the underlying entailment do not silently change
  which delaborator runs (iris additionally wraps hyps in `IrisHyp`
  because `kabstract` was stripping `.mdata` names; see iris-lean#469)

`MGoal.toExpr` round-trips with `parseMGoal?`.  `mstop` / leaving proof
mode *strips* the marker back to the real `SPred.entails`.

### Goal encoding

The Lean goal is **one** proposition, typically

```
MGoalEntails σs (hyp₁ ∧ hyp₂ ∧ …) target
```

Hypotheses are a right-nested conjunction (or Iris `sep`) with **name
metadata** on each conjunct (`parseHyp?`).  They are *not* Lean `fvar`s.
Tactics (`mintro`, `iintro`, …) rewrite this expression; InfoView
pretty-prints whatever the new type is.

Entering proof mode (`mstart`): if the current goal is already a marker,
do nothing; otherwise synthesize a tautology instance
(`PropAsSPredTautology`) and assign

```
oldGoal := start_entails newGoal
```

where `newGoal` has type `MGoal.toExpr` (empty hyp context, target `P`).

### Delaborator

mvcgen, `Lean.Elab.Tactic.Do.ProofMode.Delab`:

```lean
@[builtin_delab app.Std.Tactic.Do.MGoalEntails]
private partial def delabMGoal : Delab := do
  -- walk the conjunction, emit `mgoalHyp` lines, then:
  `(Std.Tactic.Do.mgoalStx| $hyps.reverse* ⊢ₛ $target:term)
```

User-facing syntax (also the parser used only for pretty-printing):

```lean
syntax mgoalHyp := ident " : " term
syntax mgoalStx := ppDedent(ppLine mgoalHyp)* ppDedent(ppLine "⊢ₛ " term)
```

iris-lean, `Iris.ProofMode.Display`:

```lean
@[delab app.Iris.ProofMode.Entails']
def delabIrisGoal : Delab := do
  -- persistent hyps with □, spatial with ∗
  `(irisGoalStx| $hyps.reverse* ⊢ $goal:term)
```

The Lean local context still appears **above** this block.  The extra
lines are just the pretty-printed *goal type*.  iris-lean used to draw
box-drawing separators (`──── □` / `──── ∗`); the current display
prefixes each hyp instead, so it “blends in” with Lean hyps.

`Std.Tactic.Do.Syntax` imports `ProofMode` specifically so the
`mgoalStx` grammar is in the environment.  Without it the builtin
delaborator still runs and the Goals panel looks broken.

### Hover / go-to-definition on fake hyps

Domain hyps are not Lean binders, but InfoView still wants to hover
`hP` and see a type.  Both libraries plant a **dummy local**:

```lean
def addHypInfo (stx : Syntax) (σs : Expr) (hyp : Hyp) : MetaM Unit := do
  let ty := mkApp2 (← mkConstWithFreshMVarLevels ``MGoalHypMarker) σs hyp.p
  addLocalVarInfo stx (lctx.mkLocalDecl ⟨hyp.uniq⟩ hyp.name ty) …
```

`@[delab app.…MGoalHypMarker]` (resp. `HypMarker`) unpacks the marker
so the hover shows `A`, not `MGoalHypMarker A`.  `PROP` / `SPred σs` is
not a Lean type of the hypothesis; the marker exists only so InfoView
has *something* to attach.

### What the user perceives as “custom”

* two contexts (Lean locals + stateful / SL hyps)
* a distinctive turnstile (`⊢ₛ`, `⊢` with `□`/`∗`)
* tactics that only make sense in that mode (`mintro`, `iintro`)
* the usual Goals panel, cursor tracking, and widget pretty-printer
  (subexpression highlighting still works on the delaborated syntax)

`mvcgen` itself does not custom-print VCs.  It decomposes a Hoare
triple into ordinary Lean subgoals; those that remain stateful are
shown by the proof-mode delaborator.  Concrete monads often simp the
state away, so the fancy display is most visible on monad-polymorphic
theorems.

### Sources (Lean 4 / iris-lean)

| Piece | mvcgen | iris-lean |
| --- | --- | --- |
| Marker | `Std/Tactic/Do/ProofMode.lean` | `Iris/ProofMode/Expr.lean` (`Entails'`) |
| Parse / `toExpr` | `Lean/Elab/Tactic/Do/ProofMode/MGoal.lean` | `Iris/ProofMode/Expr.lean` |
| Enter / leave | `…/ProofMode/Basic.lean` (`mstart` / `mstop`) | `istart` (often implicit) |
| Delab | `…/ProofMode/Delab.lean` | `Iris/ProofMode/Display.lean` |
| User docs | Lean reference, “The `mvcgen` tactic / Proof Mode” | `Iris/proofmode.md` |

iris-lean’s `ProofMode/Tactics.lean` comment is the other half of the
design: **display is delaboration; soundness is Lean theorems**
(`EnvsEntails`, `tac_*`) applied with `refine`.  The kernel never sees
the pretty syntax.

## Approach B — ProofWidgets panel

[ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4)
lists “alternative and domain-specific goal state displays” as a
supported use.  It sits on Lean **user widgets**:

* `@[widget_module]` — a JS/React module the infoview can load
* `PanelWidgetProps` — includes the standard `goals` / `termGoal`
* `Widget.savePanelWidgetInfo` — pin a panel at a source span
* `ppExprTagged` / `InteractiveCode` — clickable Lean expressions
  inside the widget

This is the right tool when the display is **not a pretty-printed
`Expr`**: graphs, proof trees, editable structured tactics, coloured
spatial vs persistent contexts that CSS can distinguish, etc.
iris-lean’s proof-mode rewrite even notes they hoped for “fancy HTML”
later; they did not take this path for the default goal view.

Costs that Approach A does not have:

* a JS bundle (lake/widget build)
* RPC encodable props and a round-trip for lazy pretty-printing
* an extra panel, because widgets cannot replace the built-in Goals
  renderer
* editor support is the Lean 4 infoview; nothing HOL-specific is
  required, but the UX is “Goals *and* a HOL panel”

A small widget that only *repeats* `Γ ⊢ P` as HTML is usually worse
than Approach A.  Use B when A cannot express the interaction.

## Approach C — hybrid

A practical split used elsewhere:

* **A** for the default sequent (Goals panel, cursor tracking)
* **B** for optional views (trace of `ProvTrace`, term explorer,
  Candle-style goal stack inspector)

The HOL kernel proof stays on `ProvTrace`.  The widget, if any, should
RPC the same sequents the delaborator already pretty-prints, not a
second source of truth.

## Mapping onto HOLean

HOLean sequents are `List Tm` hypotheses and a boolean conclusion, plus
a `ProvTrace` with `hole`s.  That is closer to HOL Light / Candle than
to SPred or BI.

### What Approach A would look like

1. **Turn `hby` into a term elaborator** (or a tactic inside `by`), so
   Lean records `TacticInfo`.  The command `htheorem … := hby` can
   still wrap that term.
2. **Open a display mvar** whose type is a marker, e.g.

   ```
   HolGoalEntails hyps target
   ```

   definitionally `True` (or some trivial `Prop`) *or* definitionally
   a Lean `Prop` encoding of the sequent if one exists.  The constant
   only needs to be a stable head symbol.  It must **not** be the
   kernel `Provable` — that would force a Lean proof of the HOL
   sequent in the display path.
3. **Encode hyps** as a nested pair / conjunction of `HolHypMarker`
   nodes with name metadata, analogous to `parseHyp?`.
4. **`@[delab app.HOLean.Elab.HolGoalEntails]`** producing

   ```
   h : P
   ⊢ Q
   ```

   (or HOL Light `P ?- Q` / multiple goals as multiple Lean mvars).
5. **Each HOL tactic** (`hrefl`, `happly`, …) becomes a Lean tactic
   that:
   * reads the marker via `parseHolGoal?`
   * updates `ProvTrace` / `HolTacState` as today
   * `assign`s / replaces the display mvar with the new marker type
   * uses `withTacticInfoContext` so the Goals panel snapshots
6. **Unsolved goals** are unsolved Lean mvars.  `throwError` is then
   the standard “unsolved goals” path, not a hand-rolled
   `logInfoAt` + `throwErrorAt`.
7. **`hbegin` / `htac`** can keep using a command session, or share
   the same marker encoding so `#hol_goals` is redundant with
   InfoView.

Multiple HOL subgoals should be **multiple Lean mvars** (mvcgen-style),
not one mvar whose type is a list.  The Goals panel already knows how
to list them; the delaborator only has to render one sequent.

### What not to copy blindly

* **Do not prove the display `Prop` with HOL.**  iris/mvcgen can,
  because their object logic *is* Lean `Prop`.  HOLean’s object logic
  is `Tm`.  The display marker should be inhabited by `trivial` (or
  by a proof that we do not care about), while `ProvTrace` remains
  the certificate.
* **Do not put schematic type variables and HOL terms into Lean
  locals** unless they are already there for elaboration.  Fake hyps
  via `HolHypMarker` + `addHypInfo` are enough for hover.
* **Do not depend on ProofWidgets** for the first cut.  Approach A
  is enough to stop dumping sequents into Messages.
* **Keep `logInfoAt` tests working** (`#guard_msgs`) until Goals
  snapshots are easy to golden-test; message tests and InfoView are
  different surfaces.

### Suggested order (when someone implements this)

1. Term-elaborated `hby` that opens *one* dummy `MVarId` `True` and
   wraps tactics in `withTacticInfoContext`.  Even without a custom
   delab, Goals will show *something* at the cursor.
2. Marker + delaborator for a single sequent (`Γ ⊢ P`).
3. One Lean mvar per HOL subgoal; tactics replace the focused mvar.
4. `addHypInfo` for named hypotheses.
5. (Optional) ProofWidgets panel for `ProvTrace` / the Candle stack.

Step 1 is the actual architectural change (`CommandElab` → tactic
info).  Steps 2–4 are what mvcgen/iris-lean did for display.  Step 5
is only justified if the sequent pretty-print is not enough.

## References

* Lean 4, `Lean.Elab.Tactic.Do.ProofMode.*` and `Std.Tactic.Do.ProofMode`
* Lean language reference, *The `mvcgen` tactic → Proof Mode*
* iris-lean, `Iris/proofmode.md`, `Iris/ProofMode/Display.lean`
* Lean user widgets: <https://leanprover.github.io/lean4/doc/examples/widgets.lean.html>
* ProofWidgets4 README (custom goal displays, `Expr` presentations)
* leanprover/lean4#1225 — widgets cannot replace the built-in goal view
* Nawaz, Ayers, et al., *A Graphical User Interface Framework for
  Formal Verification* (ITP 2021) — InfoView + ProofWidgets protocol
