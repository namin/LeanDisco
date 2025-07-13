import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

/-- 
Proof Curriculum: A systematic progression of statements from trivial to complex
to test and improve LeanDisco's proving capabilities.

The curriculum is organized by difficulty levels and mathematical domains.
Each level builds on the previous ones, helping identify specific gaps in proof strategies.
-/

/-- Level 1: Trivial proofs (should always work) -/
def level1_trivial : List (String × String) := [
  ("true_basic", "True"),
  ("false_implies_anything", "False → True"),
  ("identity_nat", "∀ (x : Nat), x = x"),
  ("identity_prop", "∀ (P : Prop), P → P")
]

/-- Level 2: Basic arithmetic (natural numbers) -/
def level2_arithmetic : List (String × String) := [
  ("zero_eq_zero", "0 = 0"),
  ("one_eq_one", "1 = 1"),
  ("succ_zero", "Nat.succ 0 = 1"),
  ("add_zero", "∀ (n : Nat), n + 0 = n"),
  ("zero_add", "∀ (n : Nat), 0 + n = n"),
  ("one_add_one", "1 + 1 = 2"),
  ("two_add_one", "2 + 1 = 3")
]

/-- Level 3: Function applications (from application heuristic) -/
def level3_applications : List (String × String) := [
  ("succ_of_zero", "Nat.succ 0 = 1"),
  ("succ_of_one", "Nat.succ 1 = 2"),
  ("succ_of_two", "Nat.succ 2 = 3"),
  ("add_concrete", "Nat.add 1 2 = 3"),
  ("mul_concrete", "Nat.mul 2 3 = 6"),
  ("sub_concrete", "Nat.sub 5 3 = 2")
]

/-- Level 4: Basic algebraic properties -/
def level4_algebra : List (String × String) := [
  ("add_comm_concrete", "1 + 2 = 2 + 1"),
  ("add_assoc_concrete", "(1 + 2) + 3 = 1 + (2 + 3)"),
  ("mul_comm_concrete", "2 * 3 = 3 * 2"),
  ("distributive_concrete", "2 * (3 + 4) = 2 * 3 + 2 * 4"),
  ("zero_mul", "∀ (n : Nat), 0 * n = 0"),
  ("mul_zero", "∀ (n : Nat), n * 0 = 0")
]

/-- Level 5: Simple logical reasoning -/
def level5_logic : List (String × String) := [
  ("modus_ponens", "∀ (P Q : Prop), P → (P → Q) → Q"),
  ("and_intro", "∀ (P Q : Prop), P → Q → (P ∧ Q)"),
  ("and_left", "∀ (P Q : Prop), (P ∧ Q) → P"),
  ("and_right", "∀ (P Q : Prop), (P ∧ Q) → Q"),
  ("or_left", "∀ (P Q : Prop), P → (P ∨ Q)"),
  ("or_right", "∀ (P Q : Prop), Q → (P ∨ Q)")
]

/-- Level 6: Quantifier reasoning -/
def level6_quantifiers : List (String × String) := [
  ("exists_intro", "∃ (n : Nat), n = 0"),
  ("exists_concrete", "∃ (n : Nat), n + 1 = 2"),
  ("forall_nat_zero", "∀ (n : Nat), n + 0 = n"),
  ("exists_and_forall", "∃ (m : Nat), ∀ (n : Nat), m + n = n")
]

/-- Level 7: MiniF2F-style problems (simple cases) -/
def level7_minif2f_simple : List (String × String) := [
  ("algebra_simple", "7 * (3 + 2) = 35"),
  ("numbertheory_simple", "Nat.gcd 6 9 = 3"),
  ("arithmetic_simple", "12 / 3 = 4"),
  ("polynomial_simple", "x * x = x^2")  -- Note: needs proper syntax
]

/-- Complete curriculum combining all levels -/
def proof_curriculum : List (String × String × String) := 
  (level1_trivial.map (fun (name, stmt) => ("Level1_Trivial", name, stmt))) ++
  (level2_arithmetic.map (fun (name, stmt) => ("Level2_Arithmetic", name, stmt))) ++
  (level3_applications.map (fun (name, stmt) => ("Level3_Applications", name, stmt))) ++
  (level4_algebra.map (fun (name, stmt) => ("Level4_Algebra", name, stmt))) ++
  (level5_logic.map (fun (name, stmt) => ("Level5_Logic", name, stmt))) ++
  (level6_quantifiers.map (fun (name, stmt) => ("Level6_Quantifiers", name, stmt))) ++
  (level7_minif2f_simple.map (fun (name, stmt) => ("Level7_MiniF2F", name, stmt)))

/-- Test a single curriculum item -/
def testCurriculumItem (level : String) (name : String) (stmtStr : String) : MetaM Bool := do
  IO.println s!"[CURRICULUM] Testing {level}/{name}: {stmtStr}"
  
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
  
  try
    -- Parse the statement
    let env ← getEnv
    let stx ← match Parser.runParserCategory env `term stmtStr with
      | .ok stx => pure stx
      | .error err => 
        IO.println s!"  ❌ PARSE_ERROR: {err}"
        return false
    
    let stmt ← liftTermElabM $ elabTerm stx none
    
    -- Try to prove it
    let proof ← tryProveConjecture stmt kb
    match proof with
    | some proofTerm => 
      IO.println s!"  ✅ PROVED with: {proofTerm}"
      return true
    | none => 
      IO.println s!"  ❌ FAILED to prove"
      return false
  catch e =>
    IO.println s!"  ❌ ERROR: {← e.toMessageData.toString}"
    return false

/-- Run curriculum test on a specific level -/
def testCurriculumLevel (levelName : String) : MetaM Unit := do
  IO.println s!"\n=== Testing Curriculum Level: {levelName} ==="
  
  let levelItems := proof_curriculum.filter (fun (level, _, _) => level == levelName)
  let mut passed := 0
  let mut total := 0
  
  for (level, name, stmt) in levelItems do
    let success ← testCurriculumItem level name stmt
    if success then 
      passed := passed + 1
    total := total + 1
  
  let percentage := if total > 0 then (passed * 100) / total else 0
  IO.println s!"\n{levelName} Results: {passed}/{total} passed ({percentage}%)"
  
  if passed == total then
    IO.println s!"🎉 {levelName} COMPLETE - All statements proven!"
  else
    IO.println s!"🔧 {levelName} NEEDS WORK - {total - passed} statements failed"

/-- Run full curriculum test -/
def runFullCurriculum : MetaM Unit := do
  IO.println "=== LeanDisco Proof Curriculum Test ==="
  IO.println s!"Total curriculum items: {proof_curriculum.length}"
  
  -- Test each level sequentially
  let levels := ["Level1_Trivial", "Level2_Arithmetic", "Level3_Applications", 
                "Level4_Algebra", "Level5_Logic", "Level6_Quantifiers", "Level7_MiniF2F"]
  
  let mut totalPassed := 0
  let mut totalItems := 0
  
  for level in levels do
    testCurriculumLevel level
    -- Count results for overall statistics  
    let levelItems := proof_curriculum.filter (fun (l, _, _) => l == level)
    totalItems := totalItems + levelItems.length
  
  IO.println s!"\n=== CURRICULUM SUMMARY ==="
  IO.println s!"Overall: {totalPassed}/{totalItems} statements proven"
  IO.println s!"This curriculum will guide systematic improvement of LeanDisco's proof capabilities."

/-- Quick test of just Level 1 (trivial cases) -/
def testLevel1 : MetaM Unit := do
  testCurriculumLevel "Level1_Trivial"

/-- Quick test of just Level 2 (arithmetic) -/  
def testLevel2 : MetaM Unit := do
  testCurriculumLevel "Level2_Arithmetic"

/-- Run Level 1 test -/
#eval! testLevel1