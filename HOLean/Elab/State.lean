/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lean
import HOLean.Syntax.Tm

/-!
# Current HOL environment

User `hdef` / `htheorem` declarations are stored in a Lean
`PersistentEnvExtension` and stacked on `holEnv` at the command layer.
This file does not import `Axiom`, so the elaborator can read the name
table without a module cycle.
-/

open Lean

namespace HOLean.Elab

/-- One user extension of the HOL environment. -/
inductive HolDecl where
  /-- `addDef holName ty rhs`.  `leanName` is the Lean placeholder constant. -/
  | defn (leanName : Lean.Name) (holName : HOLean.Name) (ty : Ty) (rhs : Tm)
  /-- A proved (or installed) closed boolean, named for later `Hol.thm`. -/
  | thm (leanName : Lean.Name) (holName : HOLean.Name) (stmt : Tm)
  deriving Inhabited, Repr, BEq

/-- User extensions stacked on `holEnv`, in declaration order. -/
abbrev HolState := Array HolDecl

instance : Inhabited HolState := ⟨#[]⟩

/-- Persistent HOL environment: imported modules first, then this file. -/
initialize holStateExt : SimplePersistentEnvExtension HolDecl HolState ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s d => s.push d
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

def getHolDecls [Monad m] [MonadEnv m] : m HolState := do
  return holStateExt.getState (← getEnv)

def addHolDecl [Monad m] [MonadEnv m] (d : HolDecl) : m Unit :=
  modifyEnv (holStateExt.addEntry · d)

def HolDecl.holName : HolDecl → HOLean.Name
  | .defn _ n _ _ => n
  | .thm _ n _ => n

def HolDecl.leanName : HolDecl → Lean.Name
  | .defn n _ _ _ => n
  | .thm n _ _ => n

/-- Look up a user-defined HOL constant by its Lean placeholder name. -/
def findUserDef? (env : Environment) (leanName : Lean.Name) : Option (HOLean.Name × Ty) :=
  (holStateExt.getState env).findSome? fun
    | .defn ln hn ty _ => if ln == leanName then some (hn, ty) else none
    | .thm .. => none

/-- Look up a user-defined HOL constant by its HOL name. -/
def findUserDefByHol? (decls : HolState) (holName : HOLean.Name) : Option (Ty × Tm) :=
  decls.findSome? fun
    | .defn _ hn ty rhs => if hn == holName then some (ty, rhs) else none
    | .thm .. => none

/-- Look up a user `htheorem` by its Lean placeholder name. -/
def findUserThmByLean? (env : Environment) (leanName : Lean.Name) : Option Tm :=
  (holStateExt.getState env).findSome? fun
    | .thm ln _ stmt => if ln == leanName then some stmt else none
    | .defn .. => none

/-- Look up an installed theorem by HOL or Lean name. -/
def findUserThm? (decls : HolState) (n : HOLean.Name) : Option Tm :=
  decls.findSome? fun
    | .thm ln hn stmt =>
      if hn == n || ln.toString == n then some stmt else none
    | .defn .. => none

def holNameTaken (decls : HolState) (n : HOLean.Name) : Bool :=
  decls.any (·.holName == n)

end HOLean.Elab
