import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks

/-- Simple test that loads problems and runs discovery -/
def testMiniF2FSimple : IO Unit := do
  IO.println "=== Simple MiniF2F Test ==="
  
  -- Try to load problems
  let problems ← try
    MiniF2F.loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some "valid")
  catch e =>
    IO.println s!"Could not load problems: {e}"
    pure #[]
  
  if problems.isEmpty then
    IO.println "No problems loaded - check if benchmarks directory exists"
    return
  
  IO.println s!"Successfully loaded {problems.size} problems"
  
  -- Show first few problems
  let sampleProblems := problems.take 3
  IO.println "\nSample problems:"
  for problem in sampleProblems do
    IO.println s!"- {problem.id}: {problem.formalStatement}"
  
  IO.println "\nTo run full discovery on these problems, use:"
  IO.println "#eval runMultipleProblems sampleProblems {...}"

#eval testMiniF2FSimple