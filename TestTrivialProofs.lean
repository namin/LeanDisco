import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.GoalValidation
import MiniF2F.Valid

set_option maxHeartbeats 1000000000

open LeanDisco.Benchmarks
open LeanDisco.Benchmarks.GoalValidation
open LeanDisco.Benchmarks.RealRunner
open Lean Elab Term Meta
open LeanDisco

/-- Test trivial theorems that should be provable by reflexivity -/
def testTrivialProofs : MetaM Unit := do
  IO.println "=== Testing Trivial miniF2F Theorems ===" 
  
  -- Test theorems that are proven with just "apply Eq.refl"
  let trivialTheorems := [
    "mathd_numbertheory_169",
    "mathd_numbertheory_149"
  ]
  
  let mut goals : Array Goal := #[]
  let mut successCount := 0
  
  for theoremName in trivialTheorems do
    IO.println s!"Testing theorem: {theoremName}"
    
    -- Create goal for this theorem
    let goal := createGoal theoremName theoremName
    goals := goals.push goal
    
    -- Create goal concept
    let goalConcept ← createGoalConcept goal
    IO.println s!"Created goal concept for {theoremName}"
    
    -- Try to prove it using simple discovery
    let config : DiscoveryConfig := {
      maxSpecializationDepth := 1
      maxConceptsPerIteration := 20
      pruneThreshold := 0.5
      deduplicateConcepts := true
      canonicalizeConcepts := true
      filterInternalProofs := true
      enableConjectures := true
      enablePatternRecognition := false
      enableDebugOutput := false
    }
    
    let success ← runDiscoveryWithGoals
      s!"Test_{theoremName}"
      #[goal]
      [goalConcept]
      []
      config
      3  -- 3 iterations should be enough for trivial proofs
    
    if success then
      successCount := successCount + 1
      IO.println s!"✅ SUCCESS: {theoremName} was proven!"
    else
      IO.println s!"❌ FAILED: {theoremName} could not be proven"
    
    IO.println ""
  
  let successRate := (successCount * 100) / trivialTheorems.length
  IO.println s!"=== FINAL RESULTS ==="
  IO.println s!"Tested: {trivialTheorems.length} trivial theorems"
  IO.println s!"Proven: {successCount}"
  IO.println s!"Success Rate: {successRate}%"
  
  if successCount > 0 then
    IO.println "🎉 END-TO-END PIPELINE WORKS!"
  else
    IO.println "❌ Pipeline needs more work"

/-- Run the test -/
#eval testTrivialProofs