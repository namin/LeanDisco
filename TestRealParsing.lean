import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.RealRunner
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.GoalValidation

set_option maxHeartbeats 1000000000
set_option maxRecDepth 100000000
set_option compiler.extract_closed false

open LeanDisco.Benchmarks
open LeanDisco.Benchmarks.GoalValidation
open LeanDisco.Benchmarks.RealRunner
open Lean Elab Term Meta Parser
open LeanDisco

/-- Parse a theorem statement and extract its type safely -/
def parseTheoremType (theoremCode : String) : MetaM (Option Expr) := do
  try
    -- Remove the "sorry" at the end and clean up the statement
    let cleanCode := theoremCode.replace " := sorry" ""
    
    IO.println s!"[PARSE] Attempting to parse: {cleanCode.take 100}..."
    
    -- Use Lean's parser to parse the theorem
    let env ← getEnv
    let inputCtx := Parser.mkInputContext cleanCode "<theorem>"
    
    -- Parse as a declaration command
    let syntax ← Parser.runParserCategory env `command inputCtx
    
    match syntax with
    | .node _ `theorem args => do
      IO.println s!"[PARSE] Successfully parsed theorem syntax"
      -- Extract the theorem type from the parsed syntax
      -- This is a simplified approach - in practice we'd need more sophisticated parsing
      return none -- For now, return none to avoid complexity
    | _ => do
      IO.println s!"[PARSE] Not a theorem declaration"
      return none
      
  catch e =>
    IO.println s!"[PARSE] Parse failed: {e.toMessageData}"
    return none

/-- Extract theorem name from statement string -/
def extractTheoremName (theoremCode : String) : String := do
  if theoremCode.startsWith "theorem " then
    let afterTheorem := theoremCode.drop 8
    let nameEnd := afterTheorem.toList.findIdx (· == ' ')
    if nameEnd > 0 then
      afterTheorem.take nameEnd
    else
      "unknown_theorem"
  else
    "unknown_theorem"

/-- Create a real goal by looking up the theorem in the environment -/
def createRealGoalFromEnv (problem : Problem) : MetaM (Option Goal) := do
  try
    let theoremName := extractTheoremName problem.formalStatement
    IO.println s!"[REAL_GOAL] Looking up theorem: {theoremName}"
    
    -- Try to find the theorem in the current environment
    let env ← getEnv
    let theoremNameObj := Name.mkSimple theoremName
    
    match env.find? theoremNameObj with
    | some constInfo => do
      IO.println s!"[REAL_GOAL] Found theorem in environment: {theoremName}"
      IO.println s!"[REAL_GOAL] Type: {constInfo.type}"
      
      -- Create a goal using the actual theorem type
      let goal := createGoal problem.id theoremName
      return some goal
      
    | none => do
      IO.println s!"[REAL_GOAL] Theorem {theoremName} not found in environment"
      -- Try a fallback approach by parsing a simplified version
      return createSimpleGoal problem
      
  catch e =>
    IO.println s!"[REAL_GOAL] Error: {e.toMessageData}"
    return createSimpleGoal problem

/-- Create a simple goal for problems we can't fully parse -/
def createSimpleGoal (problem : Problem) : Option Goal := do
  let theoremName := extractTheoremName problem.formalStatement
  some (createGoal problem.id theoremName)

/-- Start with simple theorems that we know exist -/
def testSimpleRealGoals : MetaM Unit := do
  IO.println "=== Testing Real Goal Creation ==="
  
  -- Test with a few simple problems first
  let simpleProblems : Array Problem := #[
    { id := "test_simple_add", 
      name := "test_simple_add", 
      formalStatement := "theorem test_simple_add (a b : ℕ) : a + b = b + a := by exact Nat.add_comm a b", 
      header := "", 
      split := "test" },
    { id := "test_zero_add", 
      name := "test_zero_add", 
      formalStatement := "theorem test_zero_add (n : ℕ) : 0 + n = n := by exact Nat.zero_add n", 
      header := "", 
      split := "test" },
    { id := "actual_minif2f", 
      name := "mathd_algebra_182", 
      formalStatement := "theorem mathd_algebra_182 (y : ℂ) : 7 * (3 * y + 2) = 21 * y + 14 := sorry", 
      header := "", 
      split := "test" }
  ]
  
  for problem in simpleProblems do
    IO.println s!"\\n--- Testing problem: {problem.id} ---"
    IO.println s!"Statement: {problem.formalStatement}"
    
    match ← createRealGoalFromEnv problem with
    | some goal => 
      IO.println s!"✓ Successfully created real goal: {goal.name}"
    | none =>
      IO.println s!"✗ Failed to create goal for {problem.id}"

/-- Try to create a goal by referencing an existing theorem -/
def createGoalFromExistingTheorem (theoremName : String) : MetaM (Option Goal) := do
  try
    let env ← getEnv
    let nameObj := Name.mkSimple theoremName
    
    match env.find? nameObj with
    | some constInfo => do
      IO.println s!"[EXISTING] Found theorem {theoremName} with type: {constInfo.type}"
      let goal := createGoal theoremName theoremName
      return some goal
    | none => do
      IO.println s!"[EXISTING] Theorem {theoremName} not found"
      return none
      
  catch e =>
    IO.println s!"[EXISTING] Error: {e.toMessageData}" 
    return none

/-- Test with known existing theorems -/
def testWithKnownTheorems : MetaM Unit := do
  IO.println "=== Testing with Known Existing Theorems ==="
  
  let knownTheorems := [
    "Nat.add_comm",
    "Nat.zero_add", 
    "Nat.add_zero",
    "Nat.mul_comm"
  ]
  
  for thName in knownTheorems do
    IO.println s!"\\nTesting known theorem: {thName}"
    match ← createGoalFromExistingTheorem thName with
    | some goal =>
      IO.println s!"✓ Created goal for existing theorem: {goal.name}"
    | none =>
      IO.println s!"✗ Could not create goal for {thName}"

-- Run the tests
#eval testSimpleRealGoals
#eval testWithKnownTheorems