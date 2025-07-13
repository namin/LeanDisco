import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

/-- Test proving a simple conjecture directly -/
def testDirectProof : MetaM Unit := do
  IO.println "=== Testing Direct Proof of Simple Conjecture ==="
  
  -- Create a simple knowledge base
  let kb : KnowledgeBase := {
    concepts := []
    iteration := 0
    failedProofs := []
    recentConcepts := []
    heuristics := { entries := [] }
    evaluators := { entries := [] }
    config := { maxSpecializationDepth := 2, maxConceptsPerIteration := 20 }
    history := []
  }
  
  -- Test 1: Create a True conjecture and try to prove it
  IO.println "\n--- Test 1: True conjecture ---"
  let trueExpr := Lean.mkConst ``True
  let trueProof ← tryProveConjecture trueExpr kb
  match trueProof with
  | some proof => 
    IO.println s!"✅ SUCCESS: Proved True with: {proof}"
  | none => 
    IO.println "❌ FAILED: Could not prove True"
  
  -- Test 2: Create a simple equality conjecture
  IO.println "\n--- Test 2: Equality conjecture (1 = 1) ---"
  let oneExpr := mkNatLit 1
  let eqExpr ← mkEq oneExpr oneExpr
  let eqProof ← tryProveConjecture eqExpr kb
  match eqProof with
  | some proof => 
    IO.println s!"✅ SUCCESS: Proved 1 = 1 with: {proof}"
  | none => 
    IO.println "❌ FAILED: Could not prove 1 = 1"
  
  -- Test 3: Create application result (succ 0 = 1)
  IO.println "\n--- Test 3: Application result (succ 0 = 1) ---"
  let zeroExpr := mkNatLit 0
  let succExpr := mkApp (Lean.mkConst ``Nat.succ) zeroExpr
  let appEqExpr ← mkEq succExpr oneExpr
  let appProof ← tryProveConjecture appEqExpr kb
  match appProof with
  | some proof => 
    IO.println s!"✅ SUCCESS: Proved succ 0 = 1 with: {proof}"
  | none => 
    IO.println "❌ FAILED: Could not prove succ 0 = 1"

  IO.println "\n=== Direct Proof Test Complete ==="

/-- Run the test -/
#eval! testDirectProof