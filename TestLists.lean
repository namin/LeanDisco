import LeanDisco.Domains.Lists

set_option maxHeartbeats 1000000000

open LeanDisco.Domains.Lists

#eval runListsDiscovery
  { maxSpecializationDepth := 3
    maxConceptsPerIteration := 50
    pruneThreshold := 0.2
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := true
    enablePatternRecognition := true
    enableDebugOutput := true }
  3  -- iterations