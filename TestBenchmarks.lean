import MiniF2F.Valid
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F
import Lean

open Lean Elab Term Meta
open LeanDisco.Benchmarks
open LeanDisco

def testBenchmarks : MetaM Unit := do
  IO.println "Testing miniF2F benchmark integration..."
  
  let testProblems : Array Problem := #[
    { id := "test_true", name := "test_true", formalStatement := "True", header := "", split := "test" },
    { id := "test_eq", name := "test_eq", formalStatement := "1 + 1 = 2", header := "", split := "test" }
  ]
  
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
  
  RealRunner.runMultipleProblems testProblems config

#eval testBenchmarks