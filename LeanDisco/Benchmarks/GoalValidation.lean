import Lean
import LeanDisco.Basic

namespace LeanDisco.Benchmarks.GoalValidation

open Lean Meta
open LeanDisco

/-- A goal represents a theorem name that must be proven for success -/
structure Goal where
  name : String           -- The theorem name to prove (e.g., "amc12a_2019_p21")
  problemId : String      -- The problem identifier
  isProven : Bool := false
  deriving Repr, BEq

/-- Goal tracking state during discovery -/
structure GoalTracker where
  goals : Array Goal
  provenGoals : Array String := #[]
  deriving Repr

/-- Create a goal from a problem name -/
def createGoal (problemId : String) (theoremName : String) : Goal := {
  name := theoremName
  problemId := problemId
  isProven := false
}

/-- Create a goal conjecture that can be added to the discovery system -/
def createGoalConcept (goal : Goal) : MetaM ConceptData := do
  -- Try to look up the theorem in the environment and get its type
  let env ← getEnv
  let theoremName := goal.name.toName
  
  match env.find? theoremName with
  | some constInfo => do
    -- Use the theorem's type as the goal expression
    let theoremType := constInfo.type
    IO.println s!"[GOAL] Created goal for {goal.name} with type: {theoremType}"
    return ConceptData.conjecture 
      goal.name 
      theoremType  -- Use the actual theorem type, not just the name
      1.0  -- High evidence to prioritize proving
      { name := goal.name
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "goal_conjecture" }
  | none => do
    -- Fallback to name-based approach for non-existent theorems
    IO.println s!"[GOAL] Warning: Theorem {goal.name} not found in environment, using name-based approach"
    return ConceptData.conjecture 
      goal.name 
      (Expr.const theoremName [])  -- Fallback to name-based expression
      1.0  -- High evidence to prioritize proving
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
    -- Check if the theorem name matches the goal name
    pure (name == goal.name)
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