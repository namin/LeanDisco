import Lean
import LeanDisco.DiscoverySystem
import Mathlib.Algebra.Group.Defs

open Lean Meta

namespace LeanDisco.Domains.GroupRing

/-- A small synthetic seed set from `Mathlib.Algebra.Group.Defs` -/
def extractGroupConcepts : MetaM (Array ConceptData) := do
  let env ← getEnv
  let all := env.constants.toList
  let relevant := all.filterMap fun (name, info) =>
    match info with
    | .thmInfo thm =>
      if name.getPrefix == `MulOneClass || name.getPrefix == `Group || name.getPrefix == `Monoid then
        some {
          name := name,
          type := thm.type,
          proof? := some thm.value,
          isDef := false,
          isProp := true,
          origin? := some "GroupRing",
          tags := ["group"],
          contexts := #[]
        }
      else none
    | _ => none
  return relevant.toArray

/-- Group/Ring domain instance -/
def GroupRingDomain : DiscoveryDomain where
  name := "GroupRing"
  seed := extractGroupConcepts

end LeanDisco.Domains.GroupRing
