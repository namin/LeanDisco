import LeanDisco.Domains.GroupRing

set_option maxHeartbeats 1000000000

open LeanDisco.Domains.GroupRing

#eval runGroupRingDiscovery
  { includeBasicGroupTheory := true
    includeCommutativeGroups := false  -- Start simple
    includeBasicRingTheory := true
    includeHomomorphisms := false }     -- Add later
  { maxSpecializationDepth := 3
    maxConceptsPerIteration := 50
    enableConjectures := true
    enablePatternRecognition := true }
  4  -- iterations