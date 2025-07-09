import LeanDisco.Benchmarks.Core
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.Simple
import LeanDisco.Benchmarks.RealRunner

namespace LeanDisco.Benchmarks

open Lean

/-- Main entry point for running benchmarks -/
def runBenchmarks (benchmarkPath : System.FilePath) 
                  (config : EvalConfig := {}) 
                  (filter : Option String := none) : IO Unit := do
  IO.println "Benchmark system is being developed..."
  IO.println "Currently only simple test is available."
  Simple.runSimpleTest

/-- Run benchmarks on a specific category -/
def runCategoryBenchmarks (benchmarkPath : System.FilePath) 
                         (category : String)
                         (config : EvalConfig := {}) : IO Unit := do
  IO.println s!"Category benchmarks for {category} not yet implemented"
  Simple.runSimpleTest

/-- Compare benchmark results between two runs -/
def compareBenchmarkRuns (beforePath : System.FilePath) (afterPath : System.FilePath) : IO Unit := do
  IO.println "Comparison feature not yet implemented"

/-- Quick test on a few problems -/
def quickTest : IO Unit := do
  RealRunner.runSimpleDiscoveryTest

end LeanDisco.Benchmarks