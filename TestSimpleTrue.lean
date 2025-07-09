import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open Lean Elab Term Meta
open LeanDisco

/-- Test that we can prove a simple True conjecture -/
def testSimpleTrue : MetaM Unit := do
  IO.println "=== Testing Simple True Conjecture Proving ==="
  
  -- Create a True conjecture directly
  let trueStmt := Expr.const ``True []
  let trueConcept := ConceptData.conjecture 
    "test_true" 
    trueStmt
    1.0
    { name := "test_true"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "test_conjecture" }
  
  IO.println "Created True conjecture"
  
  -- Run discovery with this simple conjecture
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 1
    maxConceptsPerIteration := 10
    pruneThreshold := 0.5
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := true
    enablePatternRecognition := false
    enableDebugOutput := false
  }
  
  runDiscoveryCustom
    "SimpleTrue"
    [trueConcept]
    []
    []
    3  -- Just 3 iterations
    false
    config
  
  IO.println "=== Test Complete ==="
  IO.println "Look for: '✓ Proved conjecture: test_true' in the output above"

/-- Run the test -/
#eval testSimpleTrue