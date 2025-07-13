import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Level 1: Trivial proofs that should always work
def level1_statements : List (String × Expr) := []

-- Test curriculum using pre-constructed expressions
def testSimpleCurriculum : MetaM Unit := do
  IO.println "=== Simple Proof Curriculum Test ==="
  
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
  
  -- Test 1: True
  IO.println "\n[Test 1] True"
  let trueStmt := Lean.mkConst ``True
  let proof1 ← tryProveConjecture trueStmt kb
  total := total + 1
  match proof1 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 2: 1 = 1
  IO.println "\n[Test 2] 1 = 1"
  let oneExpr := mkNatLit 1
  let eqStmt ← mkEq oneExpr oneExpr
  let proof2 ← tryProveConjecture eqStmt kb
  total := total + 1
  match proof2 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 3: 0 + 1 = 1 (application result)
  IO.println "\n[Test 3] 0 + 1 = 1"
  let zeroExpr := mkNatLit 0
  let addExpr := mkApp2 (Lean.mkConst ``Nat.add) zeroExpr oneExpr
  let arithStmt ← mkEq addExpr oneExpr
  let proof3 ← tryProveConjecture arithStmt kb
  total := total + 1
  match proof3 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 4: succ 0 = 1
  IO.println "\n[Test 4] succ 0 = 1"
  let succExpr := mkApp (Lean.mkConst ``Nat.succ) zeroExpr
  let succStmt ← mkEq succExpr oneExpr
  let proof4 ← tryProveConjecture succStmt kb
  total := total + 1
  match proof4 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 5: False → True
  IO.println "\n[Test 5] False → True"
  let falseExpr := Lean.mkConst ``False
  let trueExpr := Lean.mkConst ``True
  let implStmt ← mkArrow falseExpr trueExpr
  let proof5 ← tryProveConjecture implStmt kb
  total := total + 1
  match proof5 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Summary
  let percentage := if total > 0 then (passed * 100) / total else 0
  IO.println s!"\n=== CURRICULUM RESULTS ==="
  IO.println s!"Passed: {passed}/{total} ({percentage}%)"
  
  if passed == total then
    IO.println "🎉 ALL TESTS PASSED - Proof system is working well!"
  else
    IO.println s!"🔧 NEEDS IMPROVEMENT - {total - passed} tests failed"
    IO.println "Use these failures to systematically improve proof strategies."

-- Run the simple curriculum
#eval! testSimpleCurriculum