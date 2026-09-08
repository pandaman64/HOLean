/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Connective
import HOLean.Deduction

/-!
# Verified LCF monad

`ProveM` is a Lean stand-in for HOL Light's OCaml kernel API: failure is
`Except String` (`failwith`), the theory is a frozen `ProveCtx env`, and a
successful `CertifiedThm` carries a real `Provable` proof.
-/

namespace HOLean
namespace Prove

/-- Kernel evidence as a `Type` so `Except` / `do` work. -/
abbrev Proof (p : Prop) := PLift p

/-- A checked sequent `hyps ⊢ concl` with a kernel derivation. -/
structure CertifiedThm (env : Env) where
  hyps : List Tm
  concl : Tm
  proof : Provable env hyps concl

/-- Frozen theory for one script.  `thms` / `defs` are name rosters from
registered `HolDecl`s; evidence is still `env.axioms` / `env.constants`. -/
structure ProveCtx (env : Env) where
  wf : env.WF
  hasEq : Env.HasEq env
  conn : Env.HasConnectives env
  /-- HOL name → axiom sentence. -/
  thms : List (Name × Tm)
  /-- HOL name → generic type and defining RHS. -/
  defs : List (Name × Ty × Tm)

/-- Failure-capable computations in a fixed HOL environment. -/
abbrev ProveM (env : Env) (α : Type) :=
  ReaderT (ProveCtx env) (Except String) α

namespace ProveM

variable {env : Env}

def run (x : ProveM env α) (ctx : ProveCtx env) : Except String α :=
  ReaderT.run x ctx

def throw (msg : String) : ProveM env α :=
  fun _ => .error msg

def okProof {p : Prop} (h : p) : ProveM env (Proof p) :=
  pure ⟨h⟩

end ProveM

/-- `true` iff the computation succeeded. -/
def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

theorem isOk_ok {ε α} {a : α} : isOk (Except.ok a : Except ε α) = true :=
  rfl

theorem isOk_error {ε α} {e : ε} : isOk (Except.error e : Except ε α) = false :=
  rfl

/-- Project the `ok` payload, given that `isOk` holds. -/
def getOk {ε α} : (r : Except ε α) → isOk r = true → α
  | .ok a, _ => a
  | .error _, h => Bool.noConfusion h

/-- Extract a closed kernel theorem from a successful `ProveM`. -/
theorem extractProvable {env : Env} (ctx : ProveCtx env) (stmt : Tm)
    (m : ProveM env (Proof (Provable env [] stmt)))
    (hok : isOk (m.run ctx) = true) :
    Provable env [] stmt :=
  (getOk (m.run ctx) hok).down

end Prove
end HOLean
