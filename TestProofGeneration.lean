import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

/-- Test the proof generation mechanism directly -/
def testProofGeneration : MetaM Unit := do
  IO.println "=== Testing Proof Generation Mechanism ==="
  
  -- Create a simple knowledge base with all required fields
  let kb : KnowledgeBase := {
    concepts := []
    iteration := 0
    failedProofs := []
    recentConcepts := []
    heuristics := HeuristicRegistry.mk []
    evaluators := []
    config := DiscoveryConfig.mk
    history := []
  }
  
  -- Test 1: Prove True
  IO.println "\n--- Test 1: Proving True ---"
  let trueStmt := Lean.mkConst ``True
  let trueProof ← tryProveConjecture trueStmt kb
  match trueProof with
  | some proof => 
    IO.println s!"✅ Successfully proved True: {proof}"
  | none => 
    IO.println "❌ Failed to prove True"
  
  -- Test 2: Prove simple reflexivity 
  IO.println "\n--- Test 2: Proving 1 = 1 ---"
  let oneExpr := mkNatLit 1
  let eqStmt ← mkEq oneExpr oneExpr
  let eqProof ← tryProveConjecture eqStmt kb
  match eqProof with
  | some proof => 
    IO.println s!"✅ Successfully proved 1 = 1: {proof}"
  | none => 
    IO.println "❌ Failed to prove 1 = 1"
  
  -- Test 3: Prove 0 + 1 = 1 (arithmetic)
  IO.println "\n--- Test 3: Proving 0 + 1 = 1 ---"
  let zeroExpr := mkNatLit 0
  let addExpr := mkApp2 (Lean.mkConst ``Nat.add) zeroExpr oneExpr
  let arithStmt ← mkEq addExpr oneExpr
  let arithProof ← tryProveConjecture arithStmt kb
  match arithProof with
  | some proof => 
    IO.println s!"✅ Successfully proved 0 + 1 = 1: {proof}"
  | none => 
    IO.println "❌ Failed to prove 0 + 1 = 1"
  
  -- Test 4: Try to prove a false statement (should fail)
  IO.println "\n--- Test 4: Proving 1 = 2 (should fail) ---"
  let twoExpr := mkNatLit 2
  let falseStmt ← mkEq oneExpr twoExpr
  let falseProof ← tryProveConjecture falseStmt kb
  match falseProof with
  | some proof => 
    IO.println s!"⚠️ Unexpectedly proved 1 = 2: {proof}"
  | none => 
    IO.println "✅ Correctly failed to prove 1 = 2"

  IO.println "\n=== Proof Generation Test Complete ==="

/-- Run the test -/
#eval! testProofGeneration