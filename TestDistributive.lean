import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Test distributive property with proper variable scoping
def testDistributiveProperty : MetaM Unit := do
  IO.println "=== Testing Distributive Property ==="
  
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
  
  -- Test: 7 * (3 * y + 2) = 21 * y + 14 with proper variable scoping
  IO.println "\n[Test] 7 * (3 * y + 2) = 21 * y + 14"
  try
    withLocalDecl `y BinderInfo.default (Lean.mkConst ``Nat) fun y => do
      -- Create expressions
      let sevenExpr := mkNatLit 7
      let threeExpr := mkNatLit 3  
      let twoExpr := mkNatLit 2
      let twentyOneExpr := mkNatLit 21
      let fourteenExpr := mkNatLit 14
      
      -- Left side: 7 * (3 * y + 2)
      let three_y := mkApp2 (Lean.mkConst ``Nat.mul) threeExpr y
      let three_y_plus_2 := mkApp2 (Lean.mkConst ``Nat.add) three_y twoExpr
      let lhs := mkApp2 (Lean.mkConst ``Nat.mul) sevenExpr three_y_plus_2
      
      -- Right side: 21 * y + 14  
      let twentyone_y := mkApp2 (Lean.mkConst ``Nat.mul) twentyOneExpr y
      let rhs := mkApp2 (Lean.mkConst ``Nat.add) twentyone_y fourteenExpr
      
      -- Create equality
      let eqStmt ← mkEq lhs rhs
      IO.println s!"Trying to prove: {eqStmt}"
      
      -- Try to prove it
      let proof ← tryProveConjecture eqStmt kb
      match proof with
      | some proofTerm => 
        IO.println "✅ SUCCESS: Proved distributive property!"
        IO.println s!"Proof: {proofTerm}"
      | none => 
        IO.println "❌ FAILED: Could not prove distributive property"
        
        -- Let's also test if we can create the universal version
        let universalStmt ← mkForallFVars #[y] eqStmt
        IO.println s!"Universal version: {universalStmt}"
        let universalProof ← tryProveConjecture universalStmt kb
        match universalProof with
        | some uProof =>
          IO.println "✅ SUCCESS: Proved universal distributive property!"
          IO.println s!"Universal proof: {uProof}"
        | none =>
          IO.println "❌ FAILED: Could not prove universal distributive property"
  catch e =>
    IO.println s!"❌ ERROR: {← e.toMessageData.toString}"

-- Test simpler distributive cases first
def testSimpleDistributive : MetaM Unit := do
  IO.println "\n=== Testing Simple Distributive Cases ==="
  
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
  
  -- Test 1: 2 * (3 + 1) = 2 * 3 + 2 * 1 (concrete numbers)
  IO.println "\n[Test 1] 2 * (3 + 1) = 2 * 3 + 2 * 1"
  let twoExpr := mkNatLit 2
  let threeExpr := mkNatLit 3
  let oneExpr := mkNatLit 1
  
  let lhs1 := mkApp2 (Lean.mkConst ``Nat.mul) twoExpr (mkApp2 (Lean.mkConst ``Nat.add) threeExpr oneExpr)
  let rhs1 := mkApp2 (Lean.mkConst ``Nat.add) 
    (mkApp2 (Lean.mkConst ``Nat.mul) twoExpr threeExpr)
    (mkApp2 (Lean.mkConst ``Nat.mul) twoExpr oneExpr)
  
  let stmt1 ← mkEq lhs1 rhs1
  IO.println s!"Trying to prove: {stmt1}"
  
  let proof1 ← tryProveConjecture stmt1 kb
  match proof1 with
  | some proofTerm => 
    IO.println "✅ SUCCESS: Proved concrete distributive!"
    IO.println s!"Proof: {proofTerm}"
  | none => 
    IO.println "❌ FAILED: Could not prove concrete distributive"

-- Run both tests
def runDistributiveTests : MetaM Unit := do
  testSimpleDistributive
  testDistributiveProperty

#eval runDistributiveTests