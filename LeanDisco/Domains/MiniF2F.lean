import Lean
import MiniF2F.Valid
import LeanDisco.DiscoverySystem

open Lean Meta

namespace LeanDisco.Domains.MiniF2F

def miniF2FBlacklist : List String := [
  "mathd_numbertheory_543"
]

/-- Determine whether a constant has a complete proof (no sorry, no metavars) -/
def hasCompleteProof (info : ConstantInfo) : MetaM Bool :=
  match info with
  | .thmInfo thmInfo =>
    let axioms := thmInfo.value.getUsedConstants
    let hasMVars := thmInfo.value.hasExprMVar
    return !(axioms.contains ``sorryAx) && !hasMVars
  | _ => return false

/-- Extract theorems from the MiniF2F environment as ConceptData -/
def extractMiniF2FConcepts : MetaM (Array ConceptData) := do
  let env ← getEnv
  let allDecls := env.constants.toList
  let filtered ← allDecls.filterMapM fun (name, info) => do
    match info with
    | .thmInfo thmInfo =>
      let nameStr := name.toString
      if (nameStr.startsWith "amc" || nameStr.startsWith "mathd" || nameStr.startsWith "aime"
          || nameStr.startsWith "imo" || nameStr.startsWith "usamo" || nameStr.startsWith "induction")
          && !(miniF2FBlacklist.contains nameStr) then
        return some {
          name := name,
          type := thmInfo.type,
          proof? := none,-- some thmInfo.value,
          isDef := false,
          isProp := true,
          origin? := some "MiniF2F"
        }
      else
        return none
    | _ => return none
  return filtered.toArray

/-- MiniF2F domain instance for discovery -/
def MiniF2FDomain : DiscoveryDomain where
  name := "MiniF2F"
  seed := extractMiniF2FConcepts
  generators := [] -- extend later

end LeanDisco.Domains.MiniF2F
