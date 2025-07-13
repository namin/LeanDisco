import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

-- Test quantifier construction and proof separately
def testQuantifierConstruction : MetaM Unit := do
  IO.println "=== Testing Quantifier Construction ==="
  
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
  
  -- Test 1: Construct ∀ (x : Nat), x = x correctly
  IO.println "\n[Test 1] Constructing ∀ (x : Nat), x = x"
  try
    withLocalDecl `x BinderInfo.default (Lean.mkConst ``Nat) fun x => do
      let eq_xx ← mkEq x x
      let forall_eq ← mkForallFVars #[x] eq_xx
      IO.println s!"Successfully constructed: {forall_eq}"
      
      -- Now try to prove it
      let proof ← tryProveConjecture forall_eq kb
      match proof with
      | some proofTerm => 
        IO.println "✅ PROVED universal statement!"
        IO.println s!"Proof: {proofTerm}"
      | none => 
        IO.println "❌ FAILED to prove universal statement"
  catch e =>
    IO.println s!"❌ ERROR in construction: {← e.toMessageData.toString}"
  
  -- Test 2: Construct ∃ (x : Nat), x = 0 correctly  
  IO.println "\n[Test 2] Constructing ∃ (x : Nat), x = 0"
  try
    withLocalDecl `x BinderInfo.default (Lean.mkConst ``Nat) fun x => do
      let zeroExpr := mkNatLit 0
      let eq_x0 ← mkEq x zeroExpr
      let lambda_eq ← mkLambdaFVars #[x] eq_x0
      let exists_zero := mkApp2 (Lean.mkConst ``Exists) (Lean.mkConst ``Nat) lambda_eq
      IO.println s!"Successfully constructed: {exists_zero}"
      
      -- Now try to prove it
      let proof ← tryProveConjecture exists_zero kb
      match proof with
      | some proofTerm => 
        IO.println "✅ PROVED existential statement!"
        IO.println s!"Proof: {proofTerm}"
      | none => 
        IO.println "❌ FAILED to prove existential statement"
  catch e =>
    IO.println s!"❌ ERROR in construction: {← e.toMessageData.toString}"

#eval testQuantifierConstruction