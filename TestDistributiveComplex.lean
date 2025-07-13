import Lean
import LeanDisco.Basic
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Test distributive property with Complex numbers like mathd_algebra_182
def testComplexDistributive : MetaM Unit := do
  IO.println "=== Testing Complex Distributive Property ==="
  
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
  
  -- Test: 7 * (3 * y + 2) = 21 * y + 14 where y : ℂ
  IO.println "\n[Test] 7 * (3 * y + 2) = 21 * y + 14 (ℂ)"
  try
    withLocalDecl `y BinderInfo.default (Lean.mkConst ``Complex) fun y => do
      -- Create Complex number constants using proper universe levels
      let complexType := Lean.mkConst ``Complex
      let sevenExpr ← mkAppOptM ``OfNat.ofNat #[complexType, mkNatLit 7, none]
      let threeExpr ← mkAppOptM ``OfNat.ofNat #[complexType, mkNatLit 3, none]  
      let twoExpr ← mkAppOptM ``OfNat.ofNat #[complexType, mkNatLit 2, none]
      let twentyOneExpr ← mkAppOptM ``OfNat.ofNat #[complexType, mkNatLit 21, none]
      let fourteenExpr ← mkAppOptM ``OfNat.ofNat #[complexType, mkNatLit 14, none]
      
      -- Left side: 7 * (3 * y + 2)
      let three_y ← mkAppOptM ``HMul.hMul #[complexType, complexType, complexType, none, threeExpr, y]
      let three_y_plus_2 ← mkAppOptM ``HAdd.hAdd #[complexType, complexType, complexType, none, three_y, twoExpr]
      let lhs ← mkAppOptM ``HMul.hMul #[complexType, complexType, complexType, none, sevenExpr, three_y_plus_2]
      
      -- Right side: 21 * y + 14  
      let twentyone_y ← mkAppOptM ``HMul.hMul #[complexType, complexType, complexType, none, twentyOneExpr, y]
      let rhs ← mkAppOptM ``HAdd.hAdd #[complexType, complexType, complexType, none, twentyone_y, fourteenExpr]
      
      -- Create equality
      let eqStmt ← mkEq lhs rhs
      IO.println s!"Trying to prove: {eqStmt}"
      
      -- Try to prove it
      let proof ← tryProveConjecture eqStmt kb
      match proof with
      | some proofTerm => 
        IO.println "✅ SUCCESS: Proved complex distributive property!"
        IO.println s!"Proof: {proofTerm}"
      | none => 
        IO.println "❌ FAILED: Could not prove complex distributive property"
        IO.println "This indicates we need ring tactic support for Complex numbers"
  catch e =>
    IO.println s!"❌ ERROR: {← e.toMessageData.toString}"

-- Test simpler case with ℕ again to confirm our system works
def testNatDistributive : MetaM Unit := do
  IO.println "\n=== Testing Nat Distributive (should work) ==="
  
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
  
  -- Test: 2 * (3 + 1) = 2 * 3 + 2 * 1 (concrete Nat)
  let twoExpr := mkNatLit 2
  let threeExpr := mkNatLit 3
  let oneExpr := mkNatLit 1
  
  let lhs := mkApp2 (Lean.mkConst ``Nat.mul) twoExpr (mkApp2 (Lean.mkConst ``Nat.add) threeExpr oneExpr)
  let rhs := mkApp2 (Lean.mkConst ``Nat.add) 
    (mkApp2 (Lean.mkConst ``Nat.mul) twoExpr threeExpr)
    (mkApp2 (Lean.mkConst ``Nat.mul) twoExpr oneExpr)
  
  let stmt ← mkEq lhs rhs
  IO.println s!"Trying to prove: {stmt}"
  
  let proof ← tryProveConjecture stmt kb
  match proof with
  | some proofTerm => 
    IO.println "✅ SUCCESS: Proved Nat distributive!"
    IO.println s!"Proof: {proofTerm}"
  | none => 
    IO.println "❌ FAILED: Could not prove Nat distributive"

-- Run both tests
def runDistributiveTests : MetaM Unit := do
  testNatDistributive
  testComplexDistributive

#eval runDistributiveTests