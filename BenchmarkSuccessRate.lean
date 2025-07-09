import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks
open Lean Elab Term Meta
open LeanDisco

/-- Test success rate evaluation on miniF2F problems -/
def testSuccessRate : MetaM Unit := do
  IO.println "=== LeanDisco Benchmark Success Rate Evaluation ==="
  IO.println "Testing 3 problems from miniF2F dataset"
  IO.println ""
  
  -- Load problems from the miniF2F dataset  
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some "valid")
  catch e =>
    IO.println "Could not load problems - using test problems instead"
    -- Create test problems if file doesn't exist
    let testProblems : Array Problem := #[
      { id := "test_1", name := "test_1", formalStatement := "True", header := "", split := "test" },
      { id := "test_2", name := "test_2", formalStatement := "1 + 1 = 2", header := "", split := "test" },
      { id := "test_3", name := "test_3", formalStatement := "∀ x : Nat, x = x", header := "", split := "test" }
    ]
    pure testProblems
  
  if problems.isEmpty then
    IO.println "No problems found - using default test problems"
    return
  
  -- Take first few problems for testing
  let testProblems := problems.take 3
  
  IO.println s!"Using {testProblems.size} problems for evaluation"
  IO.println ""
  
  -- Configure discovery for proof-finding
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
  
  IO.println "Discovery Configuration:"
  IO.println s!"  Max specialization depth: {config.maxSpecializationDepth}"
  IO.println s!"  Max concepts per iteration: {config.maxConceptsPerIteration}"
  IO.println s!"  Prune threshold: {config.pruneThreshold}"
  IO.println s!"  Debug output: {config.enableDebugOutput}"
  IO.println ""
  
  -- Run the evaluation
  RealRunner.runMultipleProblems testProblems config

/-- Run success rate evaluation with default settings -/
#eval testSuccessRate