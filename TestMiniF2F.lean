import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.Metrics

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks

/-- Run miniF2F benchmark evaluation with LeanDisco -/
def runMiniF2FBenchmark (split : String) (maxProblems : Nat := 5) : MetaM Unit := do
  IO.println s!"=== MiniF2F Benchmark Evaluation ({split}) ==="
  
  -- Load problems from the miniF2F dataset
  let problems ← MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some split)
  
  if problems.isEmpty then
    IO.println s!"No problems found in split: {split}"
    return
  
  -- Take only first few problems for testing
  let testProblems := problems.take maxProblems
  
  IO.println s!"Loaded {problems.size} problems, testing first {testProblems.size}"
  IO.println ""
  
  -- Configure discovery
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 3
    maxConceptsPerIteration := 50
    pruneThreshold := 0.3
    specializationThreshold := 0.7
    maxIterations := 10
    maxTotalConcepts := 1000
    timeoutMs := 120000  -- 2 minutes per problem
    verbose := true
    enableParallelization := false
  }
  
  -- Run the evaluation using RealRunner
  let startTime ← IO.monoMsNow
  RealRunner.runMultipleProblems testProblems config
  let endTime ← IO.monoMsNow
  
  IO.println s!"\nTotal evaluation time: {endTime - startTime}ms"
  IO.println "=== Evaluation Complete ==="

/-- Test with validation split (smaller, good for testing) -/
#eval runMiniF2FBenchmark "valid" 3

/-- Uncomment to test more problems or different splits -/
-- #eval runMiniF2FBenchmark "test" 5
-- #eval runMiniF2FBenchmark "train" 2