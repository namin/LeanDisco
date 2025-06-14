import LeanDisco

set_option maxHeartbeats 10000000

open LeanDisco
open LeanDisco.Domains.GroupRing

/-- Main entry point -/
def main : IO Unit := do
  IO.println "Hello from LeanDisco!"

#eval runDiscovery 15 true

#eval runGroupRingDiscovery
      { includeBasicGroupTheory := true
        includeCommutativeGroups := false  -- Start simple
        includeBasicRingTheory := true
        includeHomomorphisms := false }     -- Add later
      { maxSpecializationDepth := 3
        maxConceptsPerIteration := 50
        enableConjectures := true
        enablePatternRecognition := true }
      15  -- iterations
