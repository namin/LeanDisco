import LeanDisco.Benchmarks.Core
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.Simple
import LeanDisco.Benchmarks.RealRunner
-- import LeanDisco.Benchmarks.Runner
-- import LeanDisco.Benchmarks.Metrics

namespace LeanDisco.Benchmarks

open Lean

/-- Main entry point for running benchmarks -/
def runBenchmarks (benchmarkPath : System.FilePath) 
                  (config : EvalConfig := {}) 
                  (filter : Option String := none) : IO Unit := do
  IO.println "Loading benchmark problems..."
  
  -- Load problems
  let problems ← MiniF2F.loadProblems benchmarkPath filter
  IO.println s!"Loaded {problems.size} problems"
  
  if problems.isEmpty then
    IO.eprintln "No problems found!"
    return
  
  -- Group by category for better reporting
  let categories := MiniF2F.groupByCategory problems
  IO.println s!"Categories: {categories.toList.map (·.1) |> String.intercalate ", "}"
  
  -- Take a small sample for testing
  let testProblems := problems.take 3
  IO.println s!"Testing with {testProblems.size} problems"
  
  IO.println "\nTo run full evaluation, use: lake lean TestMiniF2F.lean"
  IO.println "For now, running simple benchmark test..."
  
  RealRunner.runSimpleDiscoveryTest

/-- Run benchmarks on a specific category -/
def runCategoryBenchmarks (benchmarkPath : System.FilePath) 
                         (category : String)
                         (config : EvalConfig := {}) : IO Unit := do
  let problems ← MiniF2F.loadProblems benchmarkPath none
  let categoryProblems := problems.filter fun p =>
    p.category == some category
  
  if categoryProblems.isEmpty then
    IO.eprintln s!"No problems found in category: {category}"
    return
  
  IO.println s!"Found {categoryProblems.size} problems in category: {category}"
  IO.println "Use: lake lean TestMiniF2F.lean for full evaluation"
  
  RealRunner.runSimpleDiscoveryTest

/-- Compare benchmark results between two runs -/
def compareBenchmarkRuns (beforePath : System.FilePath) (afterPath : System.FilePath) : IO Unit := do
  IO.println "Loading benchmark results..."
  
  -- let before ← Metrics.loadResults beforePath
  -- let after ← Metrics.loadResults afterPath
  
  -- if before.isEmpty || after.isEmpty then
  --   IO.eprintln "Could not load results files"
  --   return
  
  -- let comparison := Metrics.compareRuns before after
  IO.println "Comparison feature temporarily disabled"
  
  -- Show newly solved problems
  -- let beforeSolved := before.filter (·.success) |>.map (·.problemId) |> List.toArray
  -- let afterSolved := after.filter (·.success) |>.map (·.problemId) |> List.toArray
  
  -- let beforeSet := beforeSolved.toList.toFinset
  -- let afterSet := afterSolved.toList.toFinset
  -- let newlySolved := (afterSet.sdiff beforeSet).toList
  
  -- if !newlySolved.isEmpty then
  --   IO.println s!"\nNewly solved problems ({newlySolved.length}):"
  --   for problemId in newlySolved do
  --     IO.println s!"  - {problemId}"

/-- Quick test on a few problems -/
def quickTest : IO Unit := do
  RealRunner.runSimpleDiscoveryTest

end LeanDisco.Benchmarks