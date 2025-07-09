import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks
open Lean Elab Term Meta
open LeanDisco

/-- Quick evaluation on a few miniF2F problems for testing -/
def quickEval (numProblems : Nat := 3) : MetaM Unit := do
  IO.println "=== LeanDisco Quick Benchmark Evaluation ==="
  IO.println s!"Testing {numProblems} problems from miniF2F dataset"
  IO.println ""
  
  -- Load problems from the miniF2F dataset  
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some "valid")
  catch e =>
    IO.println "Could not load miniF2F problems - using simple test problems"
    let testProblems : Array Problem := #[
      { id := "test_true", name := "test_true", formalStatement := "True", header := "", split := "test" },
      { id := "test_eq", name := "test_eq", formalStatement := "1 + 1 = 2", header := "", split := "test" },
      { id := "test_forall", name := "test_forall", formalStatement := "∀ x : Nat, x = x", header := "", split := "test" }
    ]
    pure testProblems
  
  let testProblems := problems.take numProblems
  
  IO.println s!"Running evaluation on {testProblems.size} problems"
  IO.println ""
  
  -- Configure discovery for proof-finding
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 25
    pruneThreshold := 0.3
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := true  -- Enable for detailed output
  }
  
  IO.println "Discovery Configuration:"
  IO.println s!"  Max specialization depth: {config.maxSpecializationDepth}"
  IO.println s!"  Max concepts per iteration: {config.maxConceptsPerIteration}"
  IO.println s!"  Enable debug output: {config.enableDebugOutput}"
  IO.println ""
  
  -- Run the evaluation
  RealRunner.runMultipleProblems testProblems config

/-- Evaluation on a specific split of problems -/
def evalSplit (split : String) (maxProblems : Nat := 10) : MetaM Unit := do
  IO.println s!"=== LeanDisco Evaluation ({split} split) ==="
  
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some split)
  catch e =>
    IO.println s!"ERROR: Could not load problems for split '{split}'"
    return
  
  if problems.isEmpty then
    IO.println s!"No problems found in split '{split}'"
    return
  
  let testProblems := problems.take maxProblems
  IO.println s!"Running evaluation on {testProblems.size} problems from {split} split"
  
  -- Optimized config for larger evaluations
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    pruneThreshold := 0.25
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := false  -- Disable for performance
  }
  
  RealRunner.runMultipleProblems testProblems config

/-- Run quick evaluation with 3 problems -/
#eval quickEval 3

/-- Uncomment to run larger evaluations: -/
-- #eval evalSplit "valid" 10
-- #eval evalSplit "test" 5

/-
Available evaluation options:
1. quickEval N - Run on N problems with debug output
2. evalSplit "split" N - Run on N problems from specific split
3. For full benchmark, use: RunFullBenchmark.lean

Current limitation: Proof validation is not implemented.
See TODO.md for details on implementing proper proof validation.
-/