/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Axiom
import HOLean.Prove.Basic
import HOLean.Prove.Typecheck
import HOLean.Prove.Kernel
import HOLean.Prove.Conv
import HOLean.Prove.Logic
import HOLean.Prove.Derived
import HOLean.Prove.Def

/-!
# Verified forward reasoning

A HOL Light-style LCF API (`ProveM`) whose successful computations return
`HasType` / `Provable` evidence.
-/

namespace HOLean
namespace Prove

/-- Context for scripts in the initial HOL environment. -/
def ProveCtx.holEnv : ProveCtx holEnv where
  wf := holEnv_WF
  hasEq := inferInstance
  conn := inferInstance
  thms := []
  defs := []

end Prove
end HOLean
