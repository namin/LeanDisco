import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.GoalValidation

set_option maxHeartbeats 1000000000

open Lean Elab Term Meta
open LeanDisco
open LeanDisco.Benchmarks.GoalValidation

/-- Test that conjecture proving mechanism works -/
def testConjectureProving : MetaM Unit := do
  IO.println "=== Testing Conjecture Proving Mechanism ==="
  
  -- Create some simple conjectures that should be provable
  let simpleGoals : Array Goal := #[
    createGoal "test1" "simple_eq_test",
    createGoal "test2" "true_test"
  ]
  
  -- Create simple goal concepts 
  let goalConcepts := simpleGoals.toList.map fun goal =>
    ConceptData.conjecture 
      goal.name 
      (Expr.const ``True [])  -- Simple True statement
      1.0
      { name := goal.name
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "test_conjecture" }
  
  IO.println s!"Created {goalConcepts.length} test conjectures"
  
  -- Run discovery with these simple conjectures
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 1
    maxConceptsPerIteration := 10
    pruneThreshold := 0.5
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := true
    enablePatternRecognition := false
    enableDebugOutput := true
  }
  
  -- Run discovery with goal validation
  let success ← runDiscoveryWithGoals
    "ConjectureTest"
    simpleGoals
    []
    []
    config
    2  -- Just 2 iterations
  
  IO.println "=== Test Complete ==="
  IO.println s!"Overall success: {success}"
  IO.println "Look for: '✓ Proved conjecture: simple_eq_test' in the output above"

/-- Run the test -/
#eval testConjectureProving