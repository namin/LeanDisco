import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

/-- Simple test of individual proof strategies -/
def simpleProofTest : MetaM Unit := do
  IO.println "=== Testing Individual Proof Strategies ==="
  
  -- Test 1: Test safeIsDefEq with True
  IO.println "\n--- Test 1: safeIsDefEq with True ---"
  let trueExpr := Lean.mkConst ``True
  let isTrue ← safeIsDefEq trueExpr trueExpr
  IO.println s!"True ≡ True: {isTrue}"
  
  -- Test 2: Test safeIsDefEq with 1 = 1
  IO.println "\n--- Test 2: safeIsDefEq with 1 = 1 ---"
  let oneExpr := mkNatLit 1
  let oneEq ← safeIsDefEq oneExpr oneExpr
  IO.println s!"1 ≡ 1: {oneEq}"
  
  -- Test 3: Test safeInferType
  IO.println "\n--- Test 3: safeInferType ---"
  let oneType ← safeInferType oneExpr
  IO.println s!"Type of 1: {oneType}"
  
  let trueType ← safeInferType trueExpr
  IO.println s!"Type of True: {trueType}"
  
  -- Test 4: Try basic equality proof construction
  IO.println "\n--- Test 4: Basic equality proof construction ---"
  try
    let eqProof ← mkAppM ``Eq.refl #[oneExpr]
    IO.println s!"✅ Created refl proof for 1 = 1: {eqProof}"
  catch e =>
    IO.println s!"❌ Failed to create refl proof: {← e.toMessageData.toString}"
    
  -- Test 5: Try True.intro construction
  IO.println "\n--- Test 5: True.intro construction ---"
  try
    let trueProof := Lean.mkConst ``True.intro
    IO.println s!"✅ Created True.intro proof: {trueProof}"
  catch e =>
    IO.println s!"❌ Failed to create True.intro proof: {← e.toMessageData.toString}"

  IO.println "\n=== Simple Proof Test Complete ==="

/-- Run the test -/
#eval! simpleProofTest