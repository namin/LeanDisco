import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks
open Lean Elab Term Meta
open LeanDisco

/-- Full benchmark evaluation on miniF2F problems -/
def runFullBenchmark : MetaM Unit := do
  IO.println "=== LeanDisco Full Benchmark Evaluation ==="
  IO.println "Loading all miniF2F problems..."
  IO.println ""
  
  -- Load problems from the miniF2F dataset  
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" none
  catch e =>
    IO.println "Could not load problems - check if benchmarks/miniF2F-lean4/minif2f_lean4.jsonl exists"
    return
  
  if problems.isEmpty then
    IO.println "No problems found - check if benchmarks directory exists"
    return
  
  IO.println s!"Loaded {problems.size} total problems from miniF2F"
  IO.println "Running evaluation on ALL problems..."
  IO.println ""
  
  -- Show split distribution
  let validProblems := problems.filter (fun p => p.split == "valid")
  let testProblems := problems.filter (fun p => p.split == "test")
  let trainProblems := problems.filter (fun p => p.split == "train")
  
  IO.println s!"Problem distribution:"
  IO.println s!"  Valid: {validProblems.size}"
  IO.println s!"  Test: {testProblems.size}"
  IO.println s!"  Train: {trainProblems.size}"
  IO.println ""
  
  -- Configure discovery for efficient full benchmark run
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 30
    pruneThreshold := 0.2
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := false  -- Disable debug for full run
  }
  
  IO.println "Discovery Configuration (optimized for full benchmark):"
  IO.println s!"  Max specialization depth: {config.maxSpecializationDepth}"
  IO.println s!"  Max concepts per iteration: {config.maxConceptsPerIteration}"
  IO.println s!"  Prune threshold: {config.pruneThreshold}"
  IO.println s!"  Debug output: {config.enableDebugOutput}"
  IO.println ""
  
  -- Run the evaluation on ALL problems
  RealRunner.runMultipleProblems problems config

/-- Quick test on just a few problems -/
def testSuccessRate : MetaM Unit := do
  IO.println "=== LeanDisco Quick Test (3 problems) ==="
  
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some "valid")
  catch e =>
    IO.println "Could not load problems - using test problems"
    let testProblems : Array Problem := #[
      { id := "test_1", name := "test_1", formalStatement := "True", header := "", split := "test" },
      { id := "test_2", name := "test_2", formalStatement := "1 + 1 = 2", header := "", split := "test" },
      { id := "test_3", name := "test_3", formalStatement := "∀ x : Nat, x = x", header := "", split := "test" }
    ]
    pure testProblems
  
  let testProblems := problems.take 3
  
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

/-- Run full benchmark evaluation (WARNING: This will take a long time!) -/
-- #eval runFullBenchmark

/-- Run quick test on 3 problems -/
#eval testSuccessRate

/-
To run the full benchmark on all problems, uncomment the line above.
This will evaluate all ~244 problems from the miniF2F dataset.
Expected time: 1-2 hours depending on system performance.
-/