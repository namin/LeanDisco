import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Test the simplest MiniF2F problem: mathd_algebra_182
-- 7 * (3 * y + 2) = 21 * y + 14 (distributive property)
def testSimplestBenchmark : MetaM Unit := do
  IO.println "=== Testing Simplest MiniF2F Problem ==="
  
  -- Create knowledge base
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
  
  -- Problem: 7 * (3 * y + 2) = 21 * y + 14
  -- Let's construct this step by step
  
  -- Create variables: y : ℂ  
  let yType := Lean.mkConst ``Complex
  
  -- Create expressions
  let sevenExpr := mkNatLit 7
  let threeExpr := mkNatLit 3  
  let twoExpr := mkNatLit 2
  let twentyOneExpr := mkNatLit 21
  let fourteenExpr := mkNatLit 14
  
  -- Create y variable (free variable for this test)
  let yVar := mkFVar (FVarId.mk (Name.mkSimple "y"))
  
  -- Left side: 7 * (3 * y + 2)
  let three_y := mkApp2 (Lean.mkConst ``HMul.hMul) threeExpr yVar
  let three_y_plus_2 := mkApp2 (Lean.mkConst ``HAdd.hAdd) three_y twoExpr
  let lhs := mkApp2 (Lean.mkConst ``HMul.hMul) sevenExpr three_y_plus_2
  
  -- Right side: 21 * y + 14
  let twentyone_y := mkApp2 (Lean.mkConst ``HMul.hMul) twentyOneExpr yVar
  let rhs := mkApp2 (Lean.mkConst ``HAdd.hAdd) twentyone_y fourteenExpr
  
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
    IO.println "This indicates we need arithmetic/ring tactics"
    
  IO.println "\n=== Analysis ==="
  IO.println "This failure shows we need:"
  IO.println "1. Distributive property support: a * (b + c) = a * b + a * c"  
  IO.println "2. Arithmetic simplification: 7 * 3 = 21, 7 * 2 = 14"
  IO.println "3. Ring theory tactics for polynomial equality"

-- Test a simpler arithmetic case first
def testBasicDistributive : MetaM Unit := do
  IO.println "\n=== Testing Basic Distributive Property ==="
  
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
  
  -- Test: 2 * (1 + 1) = 2 * 1 + 2 * 1 = 2 + 2 = 4
  let twoExpr := mkNatLit 2
  let oneExpr := mkNatLit 1
  let fourExpr := mkNatLit 4
  
  -- Left side: 2 * (1 + 1)  
  let one_plus_one := mkApp2 (Lean.mkConst ``Nat.add) oneExpr oneExpr
  let lhs := mkApp2 (Lean.mkConst ``Nat.mul) twoExpr one_plus_one
  
  -- Right side: 4
  let rhs := fourExpr
  
  let eqStmt ← mkEq lhs rhs
  IO.println s!"Trying to prove: {eqStmt}"
  
  let proof ← tryProveConjecture eqStmt kb
  match proof with
  | some proofTerm => 
    IO.println "✅ SUCCESS: Proved basic distributive!"
    IO.println s!"Proof: {proofTerm}"
  | none => 
    IO.println "❌ FAILED: Could not prove basic distributive"

-- Run both tests
def runSimpleBenchmarkTests : MetaM Unit := do
  testBasicDistributive
  testSimplestBenchmark

#eval runSimpleBenchmarkTests