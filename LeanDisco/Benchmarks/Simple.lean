import Lean
import LeanDisco.Benchmarks.Core

namespace LeanDisco.Benchmarks.Simple

open Lean

/-- Simple test runner that just tries basic tactics -/
def runSimpleTest : IO Unit := do
  let testProblems : Array Problem := #[
    { id := "test_1"
      name := "test_1"
      formalStatement := "True"
      header := ""
      split := "test"
    },
    { id := "test_2"
      name := "test_2"
      formalStatement := "1 + 1 = 2"
      header := ""
      split := "test"
    }
  ]
  
  IO.println "Running simple benchmark test..."
  
  let mut results : Array EvalResult := #[]
  
  for problem in testProblems do
    let startTime ← IO.monoMsNow
    
    -- Try to "solve" with a simple heuristic
    let success := problem.formalStatement == "True"
    let proof := if success then some "trivial" else none
    
    let endTime ← IO.monoMsNow
    
    let result : EvalResult := {
      problemId := problem.id
      success := success
      proof := proof
      timeMs := endTime - startTime
      conceptsExplored := 1
      conceptsUsed := if success then ["trivial"] else []
      heuristicsApplied := ["simple_check"]
      errorMsg := if success then none else some "Could not solve"
    }
    
    results := results.push result
    IO.println s!"Problem {problem.id}: {if success then "✓" else "✗"}"
  
  let solved := results.filter (·.success)
  IO.println s!"\nResults: {solved.size}/{results.size} problems solved"
  
  for result in results do
    IO.println s!"  {result.problemId}: {if result.success then "SUCCESS" else "FAILED"} ({result.timeMs}ms)"

end LeanDisco.Benchmarks.Simple