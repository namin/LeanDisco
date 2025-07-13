import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.GoalValidation
import MiniF2F.Valid  -- Import the actual theorem statements

set_option maxHeartbeats 1000000000
set_option maxRecDepth 100000000
set_option compiler.extract_closed false

open LeanDisco.Benchmarks
open LeanDisco.Benchmarks.GoalValidation
open LeanDisco.Benchmarks.RealRunner
open Lean Elab Term Meta
open LeanDisco

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

  -- Configure discovery (optimized for multi-goal evaluation)
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 30  -- Increased for multi-goal
    pruneThreshold := 0.3          -- Standard pruning for better exploration
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := enableDebug
  }

  -- Create goals for all problems
  IO.println "Creating goals for all problems..."
  let mut goals : Array Goal := #[]
  let mut problemConcepts : List ConceptData := []

  for problem in testProblems do
    -- Create goal for this problem
    let goalOpt ← createProblemGoal problem
    match goalOpt with
    | some goal =>
      goals := goals.push goal
      IO.println s!"✓ Created goal: {goal.name}"
    | none =>
      IO.println s!"✗ Could not create goal for {problem.id}"

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
    5   -- More iterations for multi-goal

  let endTime ← IO.monoMsNow

  if showStats then
    let totalTimeMs := endTime - startTime
    let avgTimeMs := totalTimeMs / goals.size
    IO.println s!"Multi-goal discovery completed in {totalTimeMs}ms"
    IO.println s!"Average time per goal: {avgTimeMs}ms"
    IO.println s!"Success: {success}"

-- File compiles but does not automatically run benchmarks
-- To run: use #eval runBenchmarksParallel with appropriate parameters