/-
Copyright (c) 2026 HOLean authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HOLean.Prove.Typecheck

/-!
# Definitional-extension witnesses

`certifyDef` packs every `addDef` side condition into one `ProveM`.
-/

namespace HOLean
namespace Prove

variable {env : Env}

/-- Evidence that `env.addDef n ty rhs` is a legal extension. -/
structure DefWitness (env : Env) (n : Name) (ty : Ty) (rhs : Tm) where
  fresh : env.lookup n = none
  typed : HasType env [] rhs ty
  closed : rhs.LC 0 = true
  tyvars : ∀ x ∈ rhs.tyvars, x ∈ ty.tyvars
  names : nameNotInConnectiveAndPrim n
  notFree : ∀ x α, rhs.freeIn x α = false

def certifyDef (n : Name) (ty : Ty) (rhs : Tm) :
    ProveM env (DefWitness env n ty rhs) := do
  let ⟨hfresh⟩ ← checkFreshConst n
  let ⟨ht⟩ ← checkType [] rhs ty
  let ⟨hLC⟩ ← checkClosed rhs
  let ⟨hvars⟩ ← checkTyvars ty rhs
  let ⟨hnames⟩ ← checkNameNotReserved n
  let ⟨hfree⟩ ← checkNotFree rhs
  return {
    fresh := hfresh
    typed := ht
    closed := hLC
    tyvars := hvars
    names := hnames
    notFree := hfree
  }

theorem extractDef {env : Env} (ctx : ProveCtx env) (n : Name) (ty : Ty) (rhs : Tm)
    (hok : isOk ((certifyDef n ty rhs).run ctx) = true) :
    DefWitness env n ty rhs :=
  getOk ((certifyDef n ty rhs).run ctx) hok

end Prove
end HOLean
