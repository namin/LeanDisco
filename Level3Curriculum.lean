import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Level 3: Logical reasoning and quantifiers to test proof capabilities
def testLogicCurriculum : MetaM Unit := do
  IO.println "=== Level 3 Logic Curriculum Test ==="
  
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
  
  -- Test 1: True → True
  IO.println "\n[Test 1] True → True"
  let trueExpr := Lean.mkConst ``True
  let true_impl_true ← mkArrow trueExpr trueExpr
  let proof1 ← tryProveConjecture true_impl_true kb
  total := total + 1
  match proof1 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 2: (True ∧ True) → True
  IO.println "\n[Test 2] (True ∧ True) → True"
  let andExpr := mkApp2 (Lean.mkConst ``And) trueExpr trueExpr
  let and_impl_true ← mkArrow andExpr trueExpr
  let proof2 ← tryProveConjecture and_impl_true kb
  total := total + 1
  match proof2 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 3: True → (True ∨ False)
  IO.println "\n[Test 3] True → (True ∨ False)"
  let falseExpr := Lean.mkConst ``False
  let orExpr := mkApp2 (Lean.mkConst ``Or) trueExpr falseExpr
  let true_impl_or ← mkArrow trueExpr orExpr
  let proof3 ← tryProveConjecture true_impl_or kb
  total := total + 1
  match proof3 with
  | some _ => 
    IO.println "  ✅ PASSED"
    passed := passed + 1
  | none => IO.println "  ❌ FAILED"
  
  -- Test 4: ∀ (x : Nat), x = x
  IO.println "\n[Test 4] ∀ (x : Nat), x = x"
  try
    let natType := Lean.mkConst ``Nat
    let xVar := mkBVar 0
    let eq_xx ← mkEq xVar xVar
    let forall_eq := mkForall `x BinderInfo.default natType eq_xx
    let proof4 ← tryProveConjecture forall_eq kb
    total := total + 1
    match proof4 with
    | some _ => 
      IO.println "  ✅ PASSED"
      passed := passed + 1
    | none => IO.println "  ❌ FAILED"
  catch e =>
    IO.println s!"  ❌ ERROR: {← e.toMessageData.toString}"
    total := total + 1
  
  -- Test 5: ∃ (x : Nat), x = 0
  IO.println "\n[Test 5] ∃ (x : Nat), x = 0"
  try
    let natType := Lean.mkConst ``Nat
    let zeroExpr := mkNatLit 0
    let xVar := mkBVar 0
    let eq_x0 ← mkEq xVar zeroExpr
    let exists_zero := mkApp2 (Lean.mkConst ``Exists) natType (mkLambda `x BinderInfo.default natType eq_x0)
    let proof5 ← tryProveConjecture exists_zero kb
    total := total + 1
    match proof5 with
    | some _ => 
      IO.println "  ✅ PASSED"
      passed := passed + 1
    | none => IO.println "  ❌ FAILED"
  catch e =>
    IO.println s!"  ❌ ERROR: {← e.toMessageData.toString}"
    total := total + 1
  
  -- Summary
  let percentage := if total > 0 then (passed * 100) / total else 0
  IO.println s!"\n=== LEVEL 3 LOGIC RESULTS ==="
  IO.println s!"Passed: {passed}/{total} ({percentage}%)"
  
  if passed == total then
    IO.println "🎉 LEVEL 3 COMPLETE - All logic tests passed!"
  else
    IO.println s!"🔧 LEVEL 3 NEEDS WORK - {total - passed} logic tests failed"
    IO.println "These failures indicate gaps in logical reasoning proof strategies."

-- Run the logic curriculum
#eval testLogicCurriculum