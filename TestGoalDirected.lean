import LeanDisco.Domains.GroupRing

set_option maxHeartbeats 1000000000

open LeanDisco.Domains.GroupRing

-- Test the goal-directed discovery using the GroupRing domain
-- This will now use our newly implemented goal-directed and backwards reasoning heuristics
-- which are automatically included in the standard heuristic registry

#eval runGroupRingDiscovery
  { includeBasicGroupTheory := true
    includeCommutativeGroups := false  -- Start simple
    includeBasicRingTheory := true
    includeHomomorphisms := false }     -- Add later
  { maxSpecializationDepth := 2
    maxConceptsPerIteration := 30
    enableConjectures := true
    enablePatternRecognition := true
    enableDebugOutput := true }         -- Enable debug to see goal-directed output
  2  -- Only 2 iterations for testing