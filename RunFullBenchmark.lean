import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks
open Lean Elab Term Meta
open LeanDisco

/-- Run the complete miniF2F benchmark evaluation -/
def runCompleteBenchmark : MetaM Unit := do
  IO.println "=========================================="
  IO.println "LeanDisco Complete miniF2F Benchmark"
  IO.println "=========================================="
  IO.println ""
  
  -- Load all problems from the miniF2F dataset
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" none
  catch e =>
    IO.println "ERROR: Could not load miniF2F problems!"
    IO.println "Make sure benchmarks/miniF2F-lean4/minif2f_lean4.jsonl exists"
    return
  
  if problems.isEmpty then
    IO.println "ERROR: No problems found in dataset"
    return
  
  -- Show dataset statistics
  let validProblems := problems.filter (fun p => p.split == "valid")
  let testProblems := problems.filter (fun p => p.split == "test")
  let trainProblems := problems.filter (fun p => p.split == "train")
  
  IO.println s!"Dataset Statistics:"
  IO.println s!"  Total problems: {problems.size}"
  IO.println s!"  Valid split: {validProblems.size}"
  IO.println s!"  Test split: {testProblems.size}"
  IO.println s!"  Train split: {trainProblems.size}"
  IO.println ""
  
  -- Show category distribution
  let categories := MiniF2F.groupByCategory problems
  IO.println s!"Categories:"
  for (cat, probs) in categories.toList do
    IO.println s!"  {cat}: {probs.size} problems"
  IO.println ""
  
  -- Configure discovery for full benchmark run (optimized for efficiency)
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 25
    pruneThreshold := 0.25
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := false  -- Disable debug for performance
  }
  
  IO.println "Discovery Configuration:"
  IO.println s!"  Max specialization depth: {config.maxSpecializationDepth}"
  IO.println s!"  Max concepts per iteration: {config.maxConceptsPerIteration}"
  IO.println s!"  Prune threshold: {config.pruneThreshold}"
  IO.println s!"  Debug output: {config.enableDebugOutput}"
  IO.println ""
  
  -- Estimate time
  let avgTimePerProblem := 80  -- milliseconds based on previous runs
  let estimatedTotalTime := problems.size * avgTimePerProblem
  let estimatedMinutes := estimatedTotalTime / 60000
  
  IO.println s!"Estimated evaluation time: ~{estimatedMinutes} minutes"
  IO.println "Starting full benchmark evaluation..."
  IO.println ""
  
  -- Run the complete evaluation
  let startTime ← IO.monoMsNow
  RealRunner.runMultipleProblems problems config
  let endTime ← IO.monoMsNow
  
  let totalTimeMs := endTime - startTime
  let totalMinutes := totalTimeMs / 60000
  
  IO.println ""
  IO.println "=========================================="
  IO.println "Full Benchmark Complete!"
  IO.println s!"Total time: {totalMinutes} minutes ({totalTimeMs}ms)"
  IO.println "=========================================="

/-- Run evaluation on a specific split only -/
def runSplitBenchmark (split : String) : MetaM Unit := do
  IO.println s!"=== LeanDisco Benchmark Evaluation ({split} split) ==="
  
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some split)
  catch e =>
    IO.println s!"ERROR: Could not load problems for split '{split}'"
    return
  
  if problems.isEmpty then
    IO.println s!"No problems found in split '{split}'"
    return
  
  IO.println s!"Running evaluation on {problems.size} problems from {split} split"
  
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 25
    pruneThreshold := 0.25
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false
    enablePatternRecognition := false
    enableDebugOutput := false
  }
  
  RealRunner.runMultipleProblems problems config

/-- Run the complete benchmark -/
#eval runCompleteBenchmark

/-- Uncomment to run on specific splits instead: -/
-- #eval runSplitBenchmark "valid"
-- #eval runSplitBenchmark "test"
-- #eval runSplitBenchmark "train"