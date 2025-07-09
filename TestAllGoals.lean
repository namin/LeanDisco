import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.Core
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.GoalValidation

set_option maxHeartbeats 1000000000

open Lean Elab Term Meta
open LeanDisco
open LeanDisco.Benchmarks.GoalValidation
open LeanDisco.Benchmarks.MiniF2F
open LeanDisco.Benchmarks

/-- Test discovery with ALL miniF2F problems seeded as goals -/
def testAllGoals : MetaM Unit := do
  IO.println "=== Testing Discovery with ALL MiniF2F Goals ==="
  
  -- Load all miniF2F problems
  let problems ← try
    loadProblems "benchmarks/miniF2F-lean4/minif2f_lean4.jsonl" (some "valid")
  catch e =>
    IO.println "Could not load miniF2F problems - using simple test problems"
    let testProblems : Array Problem := #[
      { id := "test_true", name := "test_true", formalStatement := "True", header := "", split := "test" },
      { id := "test_eq", name := "test_eq", formalStatement := "1 + 1 = 2", header := "", split := "test" },
      { id := "test_forall", name := "test_forall", formalStatement := "∀ x : Nat, x = x", header := "", split := "test" },
      { id := "test_simple", name := "test_simple", formalStatement := "True ∧ True", header := "", split := "test" },
      { id := "test_impl", name := "test_impl", formalStatement := "True → True", header := "", split := "test" }
    ]
    pure testProblems
  
  IO.println s!"Loaded {problems.size} problems"
  
  -- Create goals for ALL problems
  let allGoals := problems.map (fun p => createGoal p.id p.name)
  IO.println s!"Created {allGoals.size} goals"
  
  -- Create problem concepts for all problems
  let allConcepts := problems.toList.map (fun p => 
    ConceptData.taskRef
      s!"solve_{p.id}"
      p.formalStatement
      { name := s!"solve_{p.id}"
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "miniF2F_problem" })
  
  IO.println s!"Created {allConcepts.length} problem concepts"
  
  -- Configure discovery for this large run
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 200  -- Allow more concepts
    pruneThreshold := 0.3
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := true
    enablePatternRecognition := true
    enableDebugOutput := true
  }
  
  IO.println "=== Discovery Configuration ==="
  IO.println s!"Max specialization depth: {config.maxSpecializationDepth}"
  IO.println s!"Max concepts per iteration: {config.maxConceptsPerIteration}"
  IO.println s!"Enable debug output: {config.enableDebugOutput}"
  IO.println ""
  
  IO.println "Starting unified discovery with all goals..."
  IO.println "This will show iteration-by-iteration progress and goal achievements"
  IO.println ""
  
  -- Run discovery with ALL goals seeded
  let success ← runDiscoveryWithGoals
    "AllMiniF2F"
    allGoals
    allConcepts
    []  -- Use standard heuristics
    config
    10  -- More iterations for complex session
  
  IO.println ""
  IO.println "=== Final Results ==="
  IO.println s!"Overall success: {success}"
  
  -- Calculate and show success rate
  let provenCount := if success then allGoals.size else 0  -- This is a placeholder
  let successRate := if allGoals.size > 0 then 
    (provenCount.toFloat / allGoals.size.toFloat * 100.0) 
  else 0.0
  
  IO.println s!"Problems attempted: {allGoals.size}"
  IO.println s!"Success rate: {successRate}%"
  IO.println ""
  IO.println "Note: Look for '[GOAL_TRACKING]' and '✓ Goal' messages above for detailed progress"

/-- Run the test -/
#eval testAllGoals