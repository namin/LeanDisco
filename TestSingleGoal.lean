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

/-- Test if a single goal from TestBenchmarks can be proven -/
def testSingleGoal : MetaM Unit := do
  IO.println "=== Testing Single Goal: mathd_algebra_182 ===" 
  
  -- Test mathd_numbertheory_169 which is proven by Eq.refl
  let goal := createGoal "mathd_numbertheory_169" "mathd_numbertheory_169"
  
  -- Create goal concept
  let goalConcept ← createGoalConcept goal
  IO.println s!"Created goal concept for mathd_numbertheory_169"
  
  -- Use the same config as TestBenchmarks
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 30
    pruneThreshold := 0.3
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := false  -- Same as TestBenchmarks
    enablePatternRecognition := false
    enableDebugOutput := false
  }
  
  let success ← runDiscoveryWithGoals
    "SingleGoal_mathd_numbertheory_169"
    #[goal]
    [goalConcept]
    []
    config
    5  -- Same iterations as TestBenchmarks
  
  if success then
    IO.println "✅ SUCCESS: mathd_numbertheory_169 was proven!"
  else
    IO.println "❌ FAILED: mathd_numbertheory_169 could not be proven"
  
  IO.println "=== Now testing with enableConjectures := true ==="
  
  -- Test with conjectures enabled (like TestTrivialProofs)
  let config2 : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 30
    pruneThreshold := 0.3
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := true  -- Enable conjectures
    enablePatternRecognition := false
    enableDebugOutput := false
  }
  
  let success2 ← runDiscoveryWithGoals
    "SingleGoal_mathd_numbertheory_169_with_conjectures"
    #[goal]
    [goalConcept]
    []
    config2
    5
  
  if success2 then
    IO.println "✅ SUCCESS: mathd_numbertheory_169 was proven with conjectures!"
  else
    IO.println "❌ FAILED: mathd_numbertheory_169 could not be proven with conjectures"

/-- Run the test -/
#eval testSingleGoal