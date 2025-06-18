import LeanDisco.ProofConstruction

namespace TestProofConstruction

open LeanDisco LeanDisco.ProofConstruction
open Lean Meta Elab

def testProofConstruction : MetaM Unit := do
  IO.println "=== Testing Proof Construction ==="
  
  -- Test basic proof construction
  let availableTheorems := [``Nat.add_zero, ``Nat.zero_add, ``Nat.add_comm]
  
  -- Test goal: 0 = 0
  IO.println "\n🎯 Testing: 0 = 0"
  let goal1 ← generateZeroEqZero
  if let some proof ← constructProof goal1 availableTheorems then
    IO.println "✅ Successfully constructed proof for 0 = 0"
  else
    IO.println "❌ Failed to prove 0 = 0"
  
  -- Test goal: ∀ n : Nat, n + 0 = n  
  IO.println "\n🎯 Testing: ∀ n : Nat, n + 0 = n"
  let goal2 ← generateAddZeroRight
  if let some proof ← constructProof goal2 availableTheorems then
    IO.println "✅ Successfully constructed proof for n + 0 = n"
  else
    IO.println "❌ Failed to prove n + 0 = n"
  
  -- Test the heuristic
  IO.println "\n🔧 Testing proof construction heuristic"
  let concepts ← proofConstructionHeuristic {} []
  IO.println s!"Generated {concepts.length} concepts via proof construction"
  for concept in concepts do
    let name := getConceptName concept
    IO.println s!"  • {name}"

#eval testProofConstruction

end TestProofConstruction