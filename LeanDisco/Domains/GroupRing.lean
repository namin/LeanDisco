import Lean
import LeanDisco.DiscoverySystem
import Mathlib.Algebra.Group.Defs

open Lean Meta

namespace LeanDisco.Domains.GroupRing

/-- Recognizer for unary operations α → α, possibly under implicit arguments -/
def isUnaryOp (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  let rec countArrows (e : Expr) (acc : Nat) : MetaM Nat :=
    match e with
    | Expr.forallE _ _ body _ => countArrows body (acc + 1)
    | Expr.lam _ _ body _ => countArrows body (acc + 1)
    | _ => return acc
  let n ← countArrows ty 0
  return n == 1

/-- Extract relevant theorems and definitions from group-related typeclasses -/
def extractGroupConcepts : MetaM (Array ConceptData) := do
  let env ← getEnv
  let all := env.constants.toList.filter (fun (n, _) =>
    let s := n.toString
    s.startsWith "MulOneClass" || s.startsWith "Group" || s.startsWith "Monoid")
  let relevant ← all.filterMapM fun (name, info) => do
    let mut tags := ["group"]
    let (ty, val, isDef) ← match info with
      | .thmInfo thm => pure (thm.type, some thm.value, false)
      | .defnInfo defn => pure (defn.type, some defn.value, true)
      | _ => return none
    if (← isUnaryOp ty) then
      tags := "unary_op" :: tags
    return some {
      name := name,
      type := ty,
      proof? := val,
      isDef := isDef,
      isProp := !isDef,
      origin? := some "GroupRing",
      tags := tags,
      contexts := #[]
    }
  return relevant.toArray

/-- Group/Ring domain instance -/
def GroupRingDomain : DiscoveryDomain where
  name := "GroupRing"
  seed := extractGroupConcepts

end LeanDisco.Domains.GroupRing
