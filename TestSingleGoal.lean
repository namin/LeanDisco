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

/-- Test if a single goal can be proven with different configurations -/
def testSingleGoal (theoremName : String := "mathd_numbertheory_13") : MetaM Unit := do
  IO.println s!"=== Testing Single Goal: {theoremName} ===" 
  
  -- Test the specified theorem
  let goal := createGoal theoremName theoremName
  
  -- Create goal concept
  let goalConcept ← createGoalConcept goal
  IO.println s!"Created goal concept for {theoremName}"
  
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
    s!"SingleGoal_{theoremName}"
    #[goal]
    [goalConcept]
    []
    config
    5  -- Same iterations as TestBenchmarks
  
  if success then
    IO.println s!"✅ SUCCESS: {theoremName} was proven!"
  else
    IO.println s!"❌ FAILED: {theoremName} could not be proven"
  
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
    s!"SingleGoal_{theoremName}_with_conjectures"
    #[goal]
    [goalConcept]
    []
    config2
    5
  
  if success2 then
    IO.println s!"✅ SUCCESS: {theoremName} was proven with conjectures!"
  else
    IO.println s!"❌ FAILED: {theoremName} could not be proven with conjectures"

/-- Run the test with default theorem (mathd_algebra_182) -/
#eval testSingleGoal

/-- Examples of other theorems to test:
   
   Easy theorems (should work):
   #eval testSingleGoal "mathd_numbertheory_169"  -- proven by Eq.refl
   #eval testSingleGoal "mathd_numbertheory_149"  -- proven by Eq.refl
   
   Hard theorems (will likely fail):
   #eval testSingleGoal "mathd_algebra_182"       -- needs ring tactic
   #eval testSingleGoal "amc12a_2019_p21"        -- complex calculation
   #eval testSingleGoal "aime_1984_p5"           -- logarithms
   
   Usage:
   - Change the theorem name in the #eval line above
   - Run with: lake lean TestSingleGoal.lean
   - Check output for SUCCESS/FAILED messages
-/