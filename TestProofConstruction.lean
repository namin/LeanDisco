import LeanDisco.ProofGuidedSimple

namespace TestProofConstruction

open LeanDisco LeanDisco.ProofGuidedSimple
open Lean Meta Elab

/-- Generate test goal: 0 = 0 -/
def generateZeroEqZero : MetaM Expr := do
  let zero := mkConst ``Nat.zero
  return mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Nat) zero zero

/-- Generate test goal: ∀ n : Nat, n + 0 = n -/
def generateAddZeroRight : MetaM Expr := do
  let natType := mkConst ``Nat
  mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
    let add := mkConst ``Nat.add
    let zero := mkConst ``Nat.zero
    let lhs := mkApp2 add n zero
    return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n

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