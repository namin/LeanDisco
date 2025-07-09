import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks
open Lean Elab Term Meta
open LeanDisco

/-- Run benchmark evaluation with configurable options -/
def runBenchmarks 
  (numProblems : Option Nat := none)      -- none = all problems
  (split : Option String := none)         -- none = all splits  
  (enableDebug : Bool := false)           -- debug output
  (showStats : Bool := true)              -- detailed statistics
  : MetaM Unit := do
  
  IO.println "=== LeanDisco miniF2F Benchmark ==="
  
  -- Load problems
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" split
  catch e =>
    IO.println "Could not load miniF2F problems - using simple test problems"
    let testProblems : Array Problem := #[
      { id := "test_true", name := "test_true", formalStatement := "True", header := "", split := "test" },
      { id := "test_eq", name := "test_eq", formalStatement := "1 + 1 = 2", header := "", split := "test" },
      { id := "test_refl", name := "test_refl", formalStatement := "∀ x : Nat, x = x", header := "", split := "test" }
    ]
    pure testProblems
  
  if problems.isEmpty then
    IO.println "No problems found"
    return
  
  -- Limit problems if requested
  let testProblems := match numProblems with
    | some n => problems.take n
    | none => problems
  
  if showStats then
    -- Show statistics
    let splitName := split.getD "all splits"
    IO.println s!"Dataset: {testProblems.size} problems from {splitName}"
    
    if testProblems.size == problems.size then
      -- Show category distribution for full dataset
      let categories := MiniF2F.groupByCategory problems
      IO.println s!"Categories:"
      for (cat, probs) in categories.toList.take 5 do
        IO.println s!"  {cat}: {probs.size} problems"
      if categories.size > 5 then
        IO.println s!"  ... and {categories.size - 5} more categories"
    IO.println ""
  
  -- Configure discovery (optimized for performance)
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20  -- Reduced from 25
    pruneThreshold := 0.4          -- Increased from 0.3 for more aggressive pruning
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := enableDebug
  }
  
  -- Run evaluation
  let startTime ← IO.monoMsNow
  RealRunner.runMultipleProblems testProblems config
  let endTime ← IO.monoMsNow
  
  if showStats then
    let totalTimeMs := endTime - startTime
    let avgTimeMs := totalTimeMs / testProblems.size
    IO.println s!"Completed in {totalTimeMs}ms (avg {avgTimeMs}ms per problem)"

-- Run all problems by default
#eval runBenchmarks none none false true               -- ALL problems

-- Uncomment for smaller test runs:
-- #eval runBenchmarks (some 3) none false true       -- 3 problems for quick testing
-- #eval runBenchmarks (some 10) (some "valid") false true  -- 10 valid problems
-- #eval runBenchmarks (some 50) none false true      -- 50 problems

-- For development/debugging with smaller sets:
-- #eval runBenchmarks (some 1) none true true        -- 1 problem with debug output