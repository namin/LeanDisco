import MiniF2F.Valid
import LeanDisco.Benchmarks.RealRunner

open LeanDisco.Benchmarks.RealRunner

def testBenchmarks : MetaM Unit := do
  IO.println "Testing miniF2F benchmark integration..."
  
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    pruneThreshold := 0.3
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := true
  }
  
  let success ← runBenchmarkDiscovery config 3
  IO.println s!"Benchmark discovery completed: {success}"

#eval testBenchmarks