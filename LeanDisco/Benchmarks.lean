import LeanDisco.Benchmarks.Core
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.Metrics

namespace LeanDisco.Benchmarks

open Lean

/-- Load and display basic statistics about the miniF2F dataset -/
def showDatasetStats (benchmarkPath : System.FilePath) : IO Unit := do
  IO.println "=== MiniF2F Dataset Statistics ==="
  
  let problems ← try
    MiniF2F.loadProblems benchmarkPath none
  catch e =>
    IO.eprintln s!"Could not load dataset: {e}"
    return
  
  if problems.isEmpty then
    IO.eprintln "No problems found in dataset"
    return
  
  -- Show basic stats
  let validProblems := problems.filter (fun p => p.split == "valid")
  let testProblems := problems.filter (fun p => p.split == "test")
  let trainProblems := problems.filter (fun p => p.split == "train")
  
  IO.println s!"Total problems: {problems.size}"
  IO.println s!"  Valid split: {validProblems.size}"
  IO.println s!"  Test split: {testProblems.size}"
  IO.println s!"  Train split: {trainProblems.size}"
  
  -- Show categories
  let categories := MiniF2F.groupByCategory problems
  IO.println s!"\nCategories ({categories.size}):"
  for (cat, probs) in categories.toList.take 10 do
    IO.println s!"  {cat}: {probs.size} problems"
  
  IO.println "\nTo run evaluation, use:"
  IO.println "  lake lean BenchmarkEval.lean       # Quick test"
  IO.println "  lake lean RunFullBenchmark.lean    # Full evaluation"

/-- Main entry point for basic benchmark operations -/
def runBenchmarks (benchmarkPath : System.FilePath) : IO Unit := do
  showDatasetStats benchmarkPath

/-- Quick test using the RealRunner -/
def quickTest : IO Unit := do
  IO.println "=== Quick Benchmark Test ==="
  IO.println "Running simple discovery test..."
  RealRunner.runSimpleDiscoveryTest

end LeanDisco.Benchmarks