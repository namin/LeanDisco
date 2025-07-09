import LeanDisco.Benchmarks.RealRunner

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks.RealRunner

-- This shows the real integration between LeanDisco and benchmarks
#eval runBenchmarkDiscovery
  { maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    pruneThreshold := 0.3
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := true }
  3  -- iterations