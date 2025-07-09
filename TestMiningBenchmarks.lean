-- Import the miniF2F benchmarks so they're in our environment
import MiniF2F.Valid
import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.GoalValidation

set_option maxHeartbeats 1000000000

open Lean Elab Term Meta
open LeanDisco
open LeanDisco.Benchmarks.GoalValidation

/-- Test mining actual benchmark theorems from the environment -/
def testMiningBenchmarks : MetaM Unit := do
  IO.println "=== Testing Mining of Benchmark Theorems ==="
  
  -- Mine the environment for benchmark theorems
  let benchmarkPrefixes := ["mathd_", "amc", "imo_", "aime", "induction_", "algebra_", "numbertheory_"]
  let minedConcepts ← mineEnvironment benchmarkPrefixes []
  
  IO.println s!"Mined {minedConcepts.length} concepts from environment"
  
  -- Filter for theorems only
  let theorems := minedConcepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ _ => true
    | _ => false
  
  IO.println s!"Found {theorems.length} theorems"
  
  -- Show some examples
  IO.println "\n=== Sample Mined Theorems ==="
  for i in [0, 1, 2, 3, 4] do
    if h : i < theorems.length then
      let thm := theorems[i]
      match thm with
      | ConceptData.theorem name stmt _ _ _ =>
        IO.println s!"{i+1}. {name}"
        -- Test if we can prove it directly
        let kb : KnowledgeBase := { 
          concepts := [], 
          heuristics := { entries := [] },
          recentConcepts := [],
          evaluators := { entries := [] },
          config := {},
          iteration := 0,
          history := []
        }
        let proof ← tryProveConjecture stmt kb
        match proof with
        | some _ => IO.println s!"   ✓ Can be proved with tryProveConjecture!"
        | none => IO.println s!"   ✗ Cannot be proved directly"
        IO.println ""
      | _ => pure ()
  
  -- Look for our known easy cases
  IO.println "=== Looking for Easy Benchmark Cases ==="
  let easyTargets := [
    "mathd_algebra_182",
    "mathd_numbertheory_169", 
    "mathd_algebra_462",
    "mathd_numbertheory_149"
  ]
  
  for target in easyTargets do
    let found := theorems.find? fun thm => match thm with
      | ConceptData.theorem name _ _ _ _ => name == target
      | _ => false
    
    match found with
    | some (ConceptData.theorem name stmt _ _ _) =>
      IO.println s!"\nFound {name}!"
      let kb : KnowledgeBase := { 
        concepts := [], 
        heuristics := { entries := [] },
        recentConcepts := [],
        evaluators := { entries := [] },
        config := {},
        iteration := 0,
        history := []
      }
      let proof ← tryProveConjecture stmt kb
      match proof with
      | some _ => IO.println s!"✓ SUCCESS: {name} can be proved!"
      | none => IO.println s!"✗ FAILED: {name} cannot be proved"
    | _ =>
      IO.println s!"\n{target} not found in mined theorems"
  
  IO.println "\n=== Summary ==="
  IO.println "Successfully mined benchmark theorems from the environment!"
  IO.println "Next step: Use these actual theorem statements in discovery"

/-- Run the test -/
#eval testMiningBenchmarks