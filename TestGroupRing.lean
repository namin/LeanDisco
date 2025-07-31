import LeanDisco

open Lean Meta Elab

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

def myConfig : DiscoveryConfig := {
  maxIterations := 5,
  logProgress := true,
  enableProofSearch := true
}

#eval do
  let final ← runDiscovery myConfig (by exact LeanDisco.Domains.GroupRing.GroupRingDomain)
  logInfo m!"Final iteration: {final.iteration}, total concepts: {final.concepts.size}"
