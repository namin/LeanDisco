import LeanDisco.Types

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab

namespace LeanDisco

-- Structures are now imported from LeanDisco.Types
-- Utility functions for proof goal management

def addProofGoal (context : ProofContext) (goal : ProofGoal) : ProofContext :=
  { context with
    goals := goal :: context.goals.filter (fun g => g.name != goal.name) }

def updateProofGoal (context : ProofContext) (goalName : String) (update : ProofGoal → ProofGoal) : ProofContext :=
  { context with
    goals := context.goals.map fun g =>
      if g.name == goalName then update g else g }

def getActiveTargets (context : ProofContext) : List ProofGoal :=
  context.goals.filter fun g =>
    -- Active if: high priority, not too many failed attempts, and has evidence
    g.priority > 0.7 && g.evidence > 0.5 &&
    !context.recentFailures.any fun f =>
      f.statementStr == toString g.statement && f.attemptCount > 3

def conjectureToProofGoal (c : ConceptData) (iteration : Nat) : Option ProofGoal :=
  match c with
  | ConceptData.conjecture name statement evidence metadata =>
    some {
      name := name
      statement := statement
      evidence := evidence
      priority := metadata.interestingness
      iteration := iteration
    }
  | _ => none

-- Core proof functions are now in Types.lean

/-- Goal-directed concept generation heuristic - generates concepts to help prove specific goals -/
def goalDirectedHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []

  -- Extract proof context (this would come from HeuristicContext in full implementation)
  let highEvidenceConjectures := concepts.filterMap fun c => match c with
    | ConceptData.conjecture name statement evidence metadata =>
      if evidence > 0.7 then some (name, statement, evidence, metadata) else none
    | _ => none

  IO.println s!"[GOAL-DIRECTED] Found {highEvidenceConjectures.length} high-evidence conjectures to target"

  for (conjName, conjStatement, evidence, conjMeta) in highEvidenceConjectures.take 5 do
    IO.println s!"[GOAL-DIRECTED] Targeting conjecture: {conjName}"

    -- Strategy 1: Generate supporting lemmas for the conjecture
    let lemmaName := s!"lemma_for_{conjName}"
    if !concepts.any (fun c => getConceptName c == lemmaName) then
      -- Create a supporting lemma conjecture (simplified approach)
      let isValid ← isWellFormedConjecture conjStatement
      if isValid then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture lemmaName conjStatement (evidence * 0.9) {
            name := lemmaName
            created := 0
            parent := some conjName
            interestingness := evidence * 0.95
            useCount := 0
            successCount := 0
            specializationDepth := conjMeta.specializationDepth + 1
            generationMethod := "goal_directed_lemma"
          }
        ]
      else
        IO.println s!"[GOAL-DIRECTED] Skipping malformed conjecture: {lemmaName}"

    -- Strategy 2: Generate intermediate steps by analyzing the statement structure
    match conjStatement with
    | Expr.forallE varName varType body _ =>
      -- For universal statements, try to create specialized instances
      let specializedName := s!"{conjName}_specialized"
      if !concepts.any (fun c => getConceptName c == specializedName) then
        -- Look for suitable terms to instantiate with
        let suitableTerms := concepts.filterMap fun c => match c with
          | ConceptData.definition name typ _ _ _ metadata =>
            if metadata.generationMethod == "seed" || metadata.generationMethod == "mined" then
              -- Basic type checking - this is simplified
              if toString typ == toString varType then some name else none
            else none
          | _ => none

        for termName in suitableTerms.take 3 do
          let specName := s!"{conjName}_spec_{termName}"
          if !concepts.any (fun c => getConceptName c == specName) then
            let isValid ← isWellFormedConjecture body
            if isValid then
              newConcepts := newConcepts ++ [
                ConceptData.conjecture specName body (evidence * 0.8) {
                  name := specName
                  created := 0
                  parent := some conjName
                  interestingness := evidence * 0.85
                  useCount := 0
                  successCount := 0
                  specializationDepth := conjMeta.specializationDepth + 1
                  generationMethod := "goal_directed_specialization"
                }
              ]
            else
              IO.println s!"[GOAL-DIRECTED] Skipping malformed specialization: {specName}"
    | _ => pure ()

    -- Strategy 3: Generate inverse or dual concepts
    let inverseName := s!"inverse_{conjName}"
    if !concepts.any (fun c => getConceptName c == inverseName) then
      let isValid ← isWellFormedConjecture conjStatement
      if isValid then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture inverseName conjStatement (evidence * 0.7) {
            name := inverseName
            created := 0
            parent := some conjName
            interestingness := evidence * 0.8
            useCount := 0
            successCount := 0
            specializationDepth := conjMeta.specializationDepth + 1
            generationMethod := "goal_directed_inverse"
          }
        ]
      else
        IO.println s!"[GOAL-DIRECTED] Skipping malformed inverse: {inverseName}"

  -- Strategy 4: Generate concepts to fill gaps identified in failed proofs
  let failedProofPatterns := concepts.filterMap fun c => match c with
    | ConceptData.conjecture name _ evidence metadata =>
      if evidence < 0.3 && metadata.useCount > 2 then some name else none
    | _ => none

  for failedName in failedProofPatterns.take 3 do
    let bridgeName := s!"bridge_to_{failedName}"
    if !concepts.any (fun c => getConceptName c == bridgeName) then
      -- Create a bridging concept that might help prove the failed conjecture
      newConcepts := newConcepts ++ [
        ConceptData.definition bridgeName (Expr.sort Level.zero) (mkConst ``True) none [failedName] {
          name := bridgeName
          created := 0
          parent := some failedName
          interestingness := 0.6
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "goal_directed_bridge"
        }
      ]

  IO.println s!"[GOAL-DIRECTED] Generated {newConcepts.length} goal-directed concepts"
  return newConcepts

/-- Backwards reasoning heuristic - generates concepts needed to prove target theorems -/
def backwardsReasoningHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []

  -- Find theorems that might need intermediate steps
  let targetTheorems := concepts.filterMap fun c => match c with
    | ConceptData.theorem name statement _ deps metadata =>
      if metadata.specializationDepth <= 1 && deps.length > 1 then
        some (name, statement, deps, metadata)
      else none
    | _ => none

  IO.println s!"[BACKWARDS] Analyzing {targetTheorems.length} target theorems for backwards reasoning"

  for (thmName, statement, deps, metadata) in targetTheorems.take 3 do
    IO.println s!"[BACKWARDS] Working backwards from theorem: {thmName}"

    -- Strategy 1: Generate missing intermediate theorems
    for dep in deps do
      let intermediateName := s!"intermediate_for_{thmName}_via_{dep}"
      if !concepts.any (fun c => getConceptName c == intermediateName) then
        -- Create an intermediate theorem conjecture
        let isValid ← isWellFormedConjecture statement
        if isValid then
          newConcepts := newConcepts ++ [
            ConceptData.conjecture intermediateName statement 0.8 {
              name := intermediateName
              created := 0
              parent := some thmName
              interestingness := 0.85
              useCount := 0
              successCount := 0
              specializationDepth := metadata.specializationDepth + 1
              generationMethod := "backwards_reasoning_intermediate"
            }
          ]
        else
          IO.println s!"[BACKWARDS] Skipping malformed intermediate: {intermediateName}"

    -- Strategy 2: Generate helper lemmas by analyzing statement structure
    match statement with
    | Expr.forallE _ _ body _ =>
      -- For implications or universal statements, generate the antecedent as a lemma
      let antecedentName := s!"antecedent_for_{thmName}"
      if !concepts.any (fun c => getConceptName c == antecedentName) then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture antecedentName body 0.7 {
            name := antecedentName
            created := 0
            parent := some thmName
            interestingness := 0.8
            useCount := 0
            successCount := 0
            specializationDepth := metadata.specializationDepth + 1
            generationMethod := "backwards_reasoning_antecedent"
          }
        ]
    | Expr.app f arg =>
      -- For applications, generate lemmas about the function and argument
      let functionLemmaName := s!"function_lemma_for_{thmName}"
      if !concepts.any (fun c => getConceptName c == functionLemmaName) then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture functionLemmaName f 0.6 {
            name := functionLemmaName
            created := 0
            parent := some thmName
            interestingness := 0.75
            useCount := 0
            successCount := 0
            specializationDepth := metadata.specializationDepth + 1
            generationMethod := "backwards_reasoning_function"
          }
        ]
    | _ => pure ()

    -- Strategy 3: Generate dual or contrapositive statements
    let dualName := s!"dual_of_{thmName}"
    if !concepts.any (fun c => getConceptName c == dualName) then
      newConcepts := newConcepts ++ [
        ConceptData.conjecture dualName statement 0.6 {
          name := dualName
          created := 0
          parent := some thmName
          interestingness := 0.7
          useCount := 0
          successCount := 0
          specializationDepth := metadata.specializationDepth + 1
          generationMethod := "backwards_reasoning_dual"
        }
      ]

  -- Strategy 4: Generate prerequisite concepts for failed proofs
  let failedConjectures := concepts.filterMap fun c => match c with
    | ConceptData.conjecture name _ evidence metadata =>
      if evidence < 0.4 && metadata.useCount > 1 then some (name, metadata) else none
    | _ => none

  for (failedName, failedMetadata) in failedConjectures.take 2 do
    let prereqName := s!"prerequisite_for_{failedName}"
    if !concepts.any (fun c => getConceptName c == prereqName) then
      newConcepts := newConcepts ++ [
        ConceptData.definition prereqName (Expr.sort Level.zero) (mkConst ``True) none [failedName] {
          name := prereqName
          created := 0
          parent := some failedName
          interestingness := 0.65
          useCount := 0
          successCount := 0
          specializationDepth := failedMetadata.specializationDepth + 1
          generationMethod := "backwards_reasoning_prerequisite"
        }
      ]

  IO.println s!"[BACKWARDS] Generated {newConcepts.length} backwards reasoning concepts"
  return newConcepts

end LeanDisco