import Lean
import LeanDisco.Basic

namespace LeanDisco.Benchmarks.GoalValidation

open Lean Elab Term Meta
open LeanDisco

/-- A goal represents a theorem name that must be proven for success -/
structure Goal where
  name : String           -- The theorem name to prove (e.g., "amc12a_2019_p21")
  problemId : String      -- The problem identifier
  formalStatement : String -- The formal statement to prove
  isProven : Bool := false
  deriving Repr, BEq

/-- Goal tracking state during discovery -/
structure GoalTracker where
  goals : Array Goal
  provenGoals : Array String := #[]
  deriving Repr

/-- Create a goal from a problem name -/
def createGoal (problemId : String) (theoremName : String) (formalStatement : String := "") : Goal := {
  name := theoremName
  problemId := problemId
  formalStatement := formalStatement
  isProven := false
}

/-- Parse a theorem statement to extract the goal type -/
def parseTheoremStatement (statement : String) : MetaM Expr := do
  -- Simple parsing: extract theorem name if it's a full theorem statement
  -- For statements like "theorem name : type := proof", extract the name
  try
    if statement.startsWith "theorem " then
      let afterTheorem := statement.drop 8
      let nameEnd := afterTheorem.toList.findIdx (fun c => c == ' ' || c == ':')
      if nameEnd > 0 then
        let theoremName := afterTheorem.take nameEnd
        pure (Expr.const theoremName.toName [])
      else
        pure (Expr.const statement.toName [])
    else
      -- Just treat it as a theorem name
      pure (Expr.const statement.toName [])
  catch e =>
    IO.println s!"[GOAL] Failed to parse statement '{statement}': {← e.toMessageData.toString}"
    -- Ultimate fallback: create a constant
    pure (Expr.const statement.toName [])

/-- Create a goal conjecture that can be added to the discovery system -/
def createGoalConcept (goal : Goal) : MetaM ConceptData := do
  -- Try to look up the theorem in the environment and get its type
  let env ← getEnv
  let theoremName := goal.name.toName
  
  match env.find? theoremName with
  | some constInfo => do
    -- Use the theorem's type as the goal expression
    let theoremType := constInfo.type
    IO.println s!"[GOAL] Found theorem {goal.name} in environment with type: {theoremType}"
    return ConceptData.conjecture 
      goal.name 
      theoremType
      1.0
      { name := goal.name
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "goal_conjecture" }
  | none => do
    -- Parse the goal's formal statement to get the actual goal type
    let goalExpr ← parseTheoremStatement goal.formalStatement
    IO.println s!"[GOAL] Parsed goal for {goal.name} with type: {goalExpr}"
    return ConceptData.conjecture 
      goal.name 
      goalExpr
      1.0
      { name := goal.name
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "goal_conjecture" }

/-- Check if a theorem proves a specific goal -/
def theoremProvesGoal (concept : ConceptData) (goal : Goal) : MetaM Bool := do
  match concept with
  | ConceptData.theorem name statement proof deps metadata => do
    -- First check if names match
    if name != goal.name then
      pure false
    else
      -- Validate that the proof term actually proves the statement
      try
        -- Check that the proof has the correct type
        let proofType ← inferType proof
        let isValid ← isDefEq proofType statement
        if isValid then
          -- Additionally verify the proof term is well-typed
          let _ ← check proof
          IO.println s!"✓ Validated proof for {goal.name}: proof term type-checks and matches goal"
          pure true
        else
          IO.println s!"✗ Invalid proof for {goal.name}: proof type {proofType} doesn't match statement {statement}"
          pure false
      catch e =>
        IO.println s!"✗ Proof validation failed for {goal.name}: {← e.toMessageData.toString}"
        pure false
  | _ => pure false

/-- Check if any concept in the list proves the goal -/
def findProofForGoal (concepts : List ConceptData) (goal : Goal) : MetaM (Option ConceptData) := do
  for concept in concepts do
    let proves ← theoremProvesGoal concept goal
    if proves then
      return some concept
  return none

/-- Validate that all goals have been proven -/
def validateGoals (goals : Array Goal) (discoveredConcepts : List ConceptData) : MetaM (Array Bool × Array String) := do
  let mut results : Array Bool := #[]
  let mut provenGoalNames : Array String := #[]
  
  for goal in goals do
    let proof ← findProofForGoal discoveredConcepts goal
    match proof with
    | some proofConcept =>
      results := results.push true
      provenGoalNames := provenGoalNames.push goal.name
      IO.println s!"✓ Goal '{goal.name}' proven by theorem '{getConceptName proofConcept}'"
    | none =>
      results := results.push false
      IO.println s!"✗ Goal '{goal.name}' not proven"
  
  return (results, provenGoalNames)

/-- Create a goal-tracking heuristic that monitors proof progress -/
def createGoalTrackingHeuristic (goals : Array Goal) : String × HeuristicFn := 
  ("goal_tracking", fun _ concepts => do
    IO.println s!"[GOAL_TRACKING] Checking {concepts.length} concepts against {goals.size} goals"
    
    let mut goalProofs : List ConceptData := []
    
    for goal in goals do
      let proof ← findProofForGoal concepts goal
      match proof with
      | some proofConcept => 
        IO.println s!"[GOAL_TRACKING] Found proof for goal '{goal.name}': {getConceptName proofConcept}"
        -- Create a goal-specific proof concept
        let goalProof := ConceptData.theorem
          s!"proof_of_{goal.name}"
          (Expr.const goal.name.toName [])
          (match proofConcept with | ConceptData.theorem _ _ proof _ _ => proof | _ => Expr.const goal.name.toName [])
          [getConceptName proofConcept]
          { name := s!"proof_of_{goal.name}"
            created := 0
            parent := some (getConceptName proofConcept)
            interestingness := 1.5  -- High importance
            useCount := 0
            successCount := 1
            specializationDepth := 0
            generationMethod := "goal_proof" }
        goalProofs := goalProofs ++ [goalProof]
      | none => pure ()
    
    return goalProofs
  )

/-- Run discovery with goal tracking and validation -/
def runDiscoveryWithGoals 
  (problemId : String)
  (goals : Array Goal) 
  (initialConcepts : List ConceptData)
  (customHeuristics : List (String × HeuristicFn))
  (config : DiscoveryConfig := {})
  (maxIterations : Nat := 5) : MetaM Bool := do
  
  IO.println s!"=== Goal-Tracked Discovery for {problemId} ==="
  IO.println s!"Goals to prove: {goals.size}"
  for goal in goals do
    IO.println s!"  - {goal.name}"
  IO.println ""
  
  -- Create goal concepts that can be proven
  let mut goalConcepts : List ConceptData := []
  for goal in goals do
    let goalConcept ← createGoalConcept goal
    goalConcepts := goalConcepts ++ [goalConcept]
  
  -- Add goal tracking heuristic
  let goalTrackingHeuristic := createGoalTrackingHeuristic goals
  let allHeuristics := customHeuristics ++ [goalTrackingHeuristic]
  
  -- Run discovery with goals included and get final concepts
  let finalKb ← runDiscoveryCustomReturn
    s!"GoalTracker_{problemId}"
    (initialConcepts ++ goalConcepts)
    allHeuristics
    []
    maxIterations
    true  -- Enable mining for better mathematical concepts
    config
  
  IO.println s!"=== Goal Validation for {problemId} ==="
  
  -- Use the final discovered concepts from the discovery system
  let finalConcepts := finalKb.concepts
  
  -- Check if goals were proven using the discovered concepts
  let (results, _) ← validateGoals goals finalConcepts
  
  let actualProvenCount := results.filter (· == true) |>.size
  let successRate := if goals.size > 0 then 
    (actualProvenCount.toFloat / goals.size.toFloat * 100.0).toUInt8 
  else 100
  
  IO.println s!"Goal validation complete: {actualProvenCount}/{goals.size} goals proven ({successRate}%)"
  
  return actualProvenCount == goals.size

end LeanDisco.Benchmarks.GoalValidation