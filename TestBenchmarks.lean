import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.GoalValidation
import MiniF2F.Valid  -- Import the actual theorem statements

set_option maxHeartbeats 1000000000
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

open LeanDisco.Benchmarks
open LeanDisco.Benchmarks.GoalValidation
open LeanDisco.Benchmarks.RealRunner
open Lean Elab Term Meta
open LeanDisco

/-- Extract theorem name from a formal statement string -/
def extractTheoremName (theoremCode : String) : String :=
  if theoremCode.startsWith "theorem " then
    let afterTheorem := theoremCode.drop 8
    let nameEnd := afterTheorem.toList.findIdx (· == ' ')
    if nameEnd > 0 then
      afterTheorem.take nameEnd
    else
      "unknown_theorem"
  else
    "unknown_theorem"

/-- Run benchmark evaluation with all problems as goals in a single discovery session -/
def runBenchmarksParallel
  (numProblems : Option Nat := none)      -- none = all problems
  (split : Option String := none)         -- none = all splits
  (enableDebug : Bool := false)           -- debug output
  (showStats : Bool := true)              -- detailed statistics
  : MetaM Unit := do

  IO.println "=== LeanDisco miniF2F Benchmark (Multi-Goal Discovery) ==="

  -- Load problems
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" split
  catch _ =>
    IO.println "Could not load miniF2F problems - using simple test problems"
    let testProblems : Array Problem := #[
      { id := "test_true", name := "test_true", formalStatement := "True", header := "", split := "test" },
      { id := "test_eq", name := "test_eq", formalStatement := "1 + 1 = 2", header := "", split := "test" },
      { id := "test_refl", name := "test_refl", formalStatement := "∀ x : Nat, x = x", header := "", split := "test" }
    ]
    pure testProblems

  -- Add simple miniF2F theorems as sanity check
  let simpleProblems : Array Problem := #[
    { id := "test_true", name := "test_true",
      formalStatement := "True",
      header := "", split := "simple" },
    { id := "mathd_algebra_182", name := "mathd_algebra_182",
      formalStatement := "theorem mathd_algebra_182 (y : ℂ) : 7 * (3 * y + 2) = 21 * y + 14 := by ring",
      header := "", split := "simple" },
    { id := "mathd_numbertheory_169", name := "mathd_numbertheory_169",
      formalStatement := "theorem mathd_numbertheory_169 : Nat.gcd 20! 200000 = 40000 := by apply Eq.refl",
      header := "", split := "simple" }
  ]

  let allProblems := problems ++ simpleProblems

  if allProblems.isEmpty then
    IO.println "No problems found"
    return

  -- Limit problems if requested
  let testProblems := match numProblems with
    | some n => allProblems.take n
    | none => allProblems

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

  -- Configure discovery for real goal solving with full dataset
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2      -- Moderate depth for real solving
    maxConceptsPerIteration := 20     -- Reasonable concepts for 490 goals
    pruneThreshold := 0.7            -- Balanced pruning for real solving
    deduplicateConcepts := false     -- DISABLED to avoid expression equality test
    canonicalizeConcepts := false    -- DISABLED to avoid deep recursion
    filterInternalProofs := true
    enableConjectures := true        -- Enable for goal-directed discovery
    enablePatternRecognition := true -- Enable for mathematical patterns
    enableDebugOutput := enableDebug
  }

  -- Create goals for all problems
  IO.println "Creating goals for all problems..."
  let mut goals : Array Goal := #[]
  let mut problemConcepts : List ConceptData := []

  -- Process goals in smaller batches to avoid stack overflow with large datasets
  let batchSize := 20  -- Process 20 problems at a time to reduce memory pressure
  let totalBatches := (testProblems.size + batchSize - 1) / batchSize
  
  for batchIdx in [:totalBatches] do
    let startIdx := batchIdx * batchSize
    let endIdx := min (startIdx + batchSize) testProblems.size
    let batch := testProblems.toList.drop startIdx |>.take (endIdx - startIdx) |>.toArray
    
    IO.println s!"Processing batch {batchIdx + 1}/{totalBatches} (problems {startIdx + 1}-{endIdx})"
    
    for problem in batch do
      -- Create real goals using the actual theorem names from MiniF2F.Valid
      -- The theorems are already parsed and available in the environment
      let theoremName := extractTheoremName problem.formalStatement
      
      -- For the full dataset, use a safer approach that avoids deep type inspection
      -- Just create goals with the theorem names - LeanDisco can handle them
      let realGoal := createGoal problem.id theoremName
      goals := goals.push realGoal
      IO.println s!"✓ Created goal for theorem: {theoremName}"

  IO.println s!"Created {goals.size} goals from {testProblems.size} problems"
  IO.println ""

  if goals.size == 0 then
    IO.println "No valid goals created - cannot run discovery"
    return

  -- Run single discovery session with all goals
  IO.println "=== Running Multi-Goal Discovery ==="
  let startTime ← IO.monoMsNow

  let success ← runDiscoveryWithGoals
    "MultiGoalBenchmark"
    goals
    problemConcepts
    []  -- No custom heuristics
    config
    3   -- Multiple iterations for real problem solving

  let endTime ← IO.monoMsNow

  if showStats then
    let totalTimeMs := endTime - startTime
    let avgTimeMs := if goals.size > 0 then totalTimeMs / goals.size else 0
    IO.println s!"Multi-goal discovery completed in {totalTimeMs}ms"
    IO.println s!"Average time per goal: {avgTimeMs}ms"
    IO.println s!"Success: {success}"

-- NOTE: Full dataset triggers stack overflow in Lean's expression equality test
-- This occurs even with deduplication/canonicalization disabled and increased stack limits
-- The issue appears to be in Lean's internal expression comparison when loading MiniF2F.Valid
-- Maximum stable limit found: 61 problems (62+ causes stack overflow)
-- Investigation shows: The issue is cumulative complexity, not a specific problematic theorem
-- The crash occurs during compilation when loading MiniF2F.Valid, before runtime execution
-- TODO: Investigate alternative approaches to handle full 490+ problem dataset
#eval! runBenchmarksParallel (some 61) none false true  -- Maximum stable limit: 61 problems

-- Test with simple theorems first as sanity check:
-- #eval runBenchmarksParallel (some 5) none false true       -- 5 problems including simple ones
-- #eval runBenchmarksParallel (some 10) (some "valid") false true  -- 10 valid problems as goals
-- #eval runBenchmarksParallel (some 50) none false true      -- 50 problems as goals

-- For development/debugging with smaller sets:
-- #eval runBenchmarksParallel (some 1) none true true        -- 1 problem with debug output
