import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open Lean Elab Term Meta
open LeanDisco

/-- Test the mining infrastructure with existing environment -/
def testMiningInfra : MetaM Unit := do
  IO.println "=== Testing Mining Infrastructure ==="
  
  -- Mine the environment for Nat-related theorems
  let natPrefixes := ["Nat.zero", "Nat.succ", "Nat.add", "Nat.gcd", "Nat.mul"]
  let minedConcepts ← mineEnvironment natPrefixes []
  
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
        IO.println s!"   Statement: {stmt}"
        -- Try to prove this theorem
        let kb : KnowledgeBase := { 
          concepts := minedConcepts, 
          heuristics := { entries := [] },
          recentConcepts := [],
          evaluators := { entries := [] },
          config := {},
          iteration := 0,
          history := []
        }
        let proof ← tryProveConjecture stmt kb
        match proof with
        | some _ => IO.println s!"   ✓ Can be proved!"
        | none => IO.println s!"   ✗ Cannot be proved"
        IO.println ""
      | _ => pure ()
  
  -- Test that we can find computational theorems
  IO.println "=== Checking for GCD-related theorems ==="
  let gcdTheorems := theorems.filter fun thm => match thm with
    | ConceptData.theorem name _ _ _ _ => "gcd".isPrefixOf name.toLower
    | _ => false
  
  IO.println s!"Found {gcdTheorems.length} GCD-related theorems"
  
  for thm in gcdTheorems.take 3 do
    match thm with
    | ConceptData.theorem name stmt _ _ _ =>
      IO.println s!"- {name}: {stmt}"
    | _ => pure ()
  
  IO.println "\n=== Summary ==="
  IO.println "The mining infrastructure works and can extract theorem statements."
  IO.println "For benchmarks, we need to either:"
  IO.println "1. Add miniF2F as a dependency in lakefile.toml"
  IO.println "2. Or parse the benchmark statements directly from the .lean files"

/-- Run the test -/
#eval testMiningInfra