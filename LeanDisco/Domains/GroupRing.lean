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

/-- Heuristic: generate idempotence conjectures for tagged unary_ops -/
def heuristicIdempotenceConjectures (state : DiscoveryState) : MetaM DiscoveryStateDelta := do
  let candidates := state.newConcepts.filter (fun c => "unary_op" ∈ c.tags && c.proof?.isSome)

  let conjects ← candidates.filterMapM fun f => do
    try
      let fConst := mkConst f.name
      let ty ← whnf f.type
      match ty with
      | Expr.forallE _ dom _ _ =>
        withLocalDeclD `x dom fun x => do
          let fx := mkApp fConst x
          let ffx := mkApp fConst fx
          let stmt := mkApp3 (mkConst ``Eq) dom ffx x
          let quantified ← mkForallFVars #[x] stmt
          let name := f.name.appendAfter "_idem_conj"
          return some {
            name := name,
            type := quantified,
            proof? := none,
            isDef := false,
            isProp := true,
            origin? := some "heuristicIdempotenceConjectures",
            tags := ["generated", "idempotence"],
            contexts := #[]
          }
      | _ => return none
    catch _ => return none

  return { newConcepts := conjects }

end LeanDisco.Domains.GroupRing
