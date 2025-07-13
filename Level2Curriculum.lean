import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Level 2: Arithmetic tests to identify arithmetic proof gaps
def testArithmeticCurriculum : MetaM Unit := do
  IO.println "=== Level 2 Arithmetic Curriculum Test ==="
  
  -- Create simple knowledge base
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
  
  let mut passed := 0
  let mut total := 0
  
  -- Test 1: 0 = 0
  IO.println "\n[Test 1] 0 = 0"
  let zeroExpr := mkNatLit 0
  let zero_eq_zero ← mkEq zeroExpr zeroExpr
  let proof1 ← tryProveConjecture zero_eq_zero kb
  total := total + 1
  match proof1 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 2: 2 = 2  
  IO.println "\n[Test 2] 2 = 2"
  let twoExpr := mkNatLit 2
  let two_eq_two ← mkEq twoExpr twoExpr
  let proof2 ← tryProveConjecture two_eq_two kb
  total := total + 1
  match proof2 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 3: 1 + 1 = 2
  IO.println "\n[Test 3] 1 + 1 = 2"
  let oneExpr := mkNatLit 1
  let addExpr := mkApp2 (Lean.mkConst ``Nat.add) oneExpr oneExpr
  let add_stmt ← mkEq addExpr twoExpr
  let proof3 ← tryProveConjecture add_stmt kb
  total := total + 1
  match proof3 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 4: 2 + 1 = 3
  IO.println "\n[Test 4] 2 + 1 = 3"
  let threeExpr := mkNatLit 3
  let add2_expr := mkApp2 (Lean.mkConst ``Nat.add) twoExpr oneExpr
  let add2_stmt ← mkEq add2_expr threeExpr
  let proof4 ← tryProveConjecture add2_stmt kb
  total := total + 1
  match proof4 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 5: 2 * 3 = 6
  IO.println "\n[Test 5] 2 * 3 = 6"
  let sixExpr := mkNatLit 6
  let mulExpr := mkApp2 (Lean.mkConst ``Nat.mul) twoExpr threeExpr
  let mul_stmt ← mkEq mulExpr sixExpr
  let proof5 ← tryProveConjecture mul_stmt kb
  total := total + 1
  match proof5 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Summary
  let percentage := if total > 0 then (passed * 100) / total else 0
  IO.println s!"\n=== LEVEL 2 ARITHMETIC RESULTS ==="
  IO.println s!"Passed: {passed}/{total} ({percentage}%)"
  
  if passed == total then
    IO.println "🎉 LEVEL 2 COMPLETE - All arithmetic tests passed!"
  else
    IO.println s!"🔧 LEVEL 2 NEEDS WORK - {total - passed} arithmetic tests failed"
    IO.println "These failures indicate gaps in arithmetic proof strategies."

-- Run the arithmetic curriculum
#eval testArithmeticCurriculum