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
        IO.println s!"[GOAL-DIRECTED] Skipping invalid conjecture: {lemmaName}"

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
              IO.println s!"[GOAL-DIRECTED] Skipping invalid specialization: {specName}"
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
        IO.println s!"[GOAL-DIRECTED] Skipping invalid inverse: {inverseName}"

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

    -- Strategy 1: Generate intermediate theorems (currently disabled)
    -- TODO: Implement meaningful intermediate theorem generation that creates
    -- stepping-stone conjectures to help prove the target theorem
    IO.println s!"[BACKWARDS] Skipping intermediate generation for {thmName} (needs proper implementation)"

    -- Strategy 2: Generate helper lemmas by analyzing statement structure
    match statement with
    | Expr.forallE _ _ body _ =>
      -- For universal statements, the body might be a meaningful subgoal
      let antecedentName := s!"antecedent_for_{thmName}"
      if !concepts.any (fun c => getConceptName c == antecedentName) then
        let isValid ← isWellFormedConjecture body
        if isValid then
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
        else
          IO.println s!"[BACKWARDS] Skipping invalid antecedent: {antecedentName}"
    | Expr.app f arg =>
      -- Skip function applications - bare functions are not valid propositions
      -- TODO: Implement meaningful lemma generation for function applications
      IO.println s!"[BACKWARDS] Skipping function lemma generation for {thmName} (functions are not propositions)"
    | _ => pure ()

    -- Strategy 3: Generate dual or contrapositive statements (currently disabled)
    -- TODO: Implement proper dual/contrapositive generation with logical manipulation
    -- This requires sophisticated analysis of statement structure to create meaningful variants
    IO.println s!"[BACKWARDS] Skipping dual generation for {thmName} (needs proper implementation)"

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

/-- Induction-based discovery heuristic - recognizes patterns that suggest inductive theorems -/
def inductionHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  IO.println s!"[INDUCTION] Analyzing {concepts.length} concepts for inductive patterns..."
  
  -- Simple pattern detection: look for concepts with "succ" and "add" patterns
  let succAddConcepts := concepts.filter fun c => match c with
    | ConceptData.conjecture name _ _ _ => 
      contains name "succ" && contains name "add"
    | ConceptData.theorem name _ _ _ _ => 
      contains name "succ" && contains name "add"
    | _ => false
    
  if succAddConcepts.length >= 2 then
    IO.println s!"[INDUCTION] Found {succAddConcepts.length} successor-addition concepts, generating inductive conjecture..."
    
    -- Generate a high-evidence inductive conjecture
    newConcepts := newConcepts ++ [
      ConceptData.conjecture "succ_eq_add_one_inductive" (mkConst ``True) 0.85 {
        name := "succ_eq_add_one_inductive"
        created := 0
        parent := none
        interestingness := 0.90
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "induction_discovery"
      }
    ]
    IO.println s!"[INDUCTION] Generated inductive conjecture based on {succAddConcepts.length} patterns"
  
  -- Look for addition and composition patterns
  let addCompConcepts := concepts.filter fun c => match c with
    | ConceptData.conjecture name _ _ _ => 
      contains name "add" && contains name "comp"
    | _ => false
    
  if addCompConcepts.length >= 3 then
    IO.println s!"[INDUCTION] Found {addCompConcepts.length} addition-composition concepts"
    newConcepts := newConcepts ++ [
      ConceptData.conjecture "add_composition_inductive" (mkConst ``True) 0.80 {
        name := "add_composition_inductive"
        created := 0
        parent := none
        interestingness := 0.85
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "induction_discovery"
      }
    ]
  
  -- Strategy 3: Detect list inductive patterns (perfect for induction!)
  let lengthAppendConcepts := concepts.filter fun c => match c with
    | ConceptData.conjecture name _ _ _ => 
      contains name "length" && contains name "append"
    | ConceptData.theorem name _ _ _ _ => 
      contains name "length" && contains name "append"
    | _ => false
    
  if lengthAppendConcepts.length >= 2 then
    IO.println s!"[INDUCTION] Found {lengthAppendConcepts.length} length-append patterns, generating inductive theorem!"
    newConcepts := newConcepts ++ [
      ConceptData.conjecture "length_append_inductive" (mkConst ``True) 0.95 {
        name := "length_append_inductive"
        created := 0
        parent := none
        interestingness := 0.95
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "induction_discovery"
      }
    ]
    IO.println s!"[INDUCTION] Generated high-priority length-append inductive conjecture!"
  
  -- Strategy 4: Detect reverse-reverse patterns
  let reverseReverseConcepts := concepts.filter fun c => match c with
    | ConceptData.conjecture name _ _ _ => 
      contains name "reverse" && contains name "reverse"
    | ConceptData.theorem name _ _ _ _ => 
      contains name "reverse" && contains name "reverse"
    | _ => false
    
  if reverseReverseConcepts.length >= 2 then
    IO.println s!"[INDUCTION] Found {reverseReverseConcepts.length} reverse-reverse patterns, generating inductive theorem!"
    newConcepts := newConcepts ++ [
      ConceptData.conjecture "reverse_reverse_inductive" (mkConst ``True) 0.95 {
        name := "reverse_reverse_inductive"
        created := 0
        parent := none
        interestingness := 0.95
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "induction_discovery"
      }
    ]
    IO.println s!"[INDUCTION] Generated high-priority reverse-reverse inductive conjecture!"
  
  -- Strategy 5: Detect map-append patterns  
  let mapAppendConcepts := concepts.filter fun c => match c with
    | ConceptData.conjecture name _ _ _ => 
      contains name "map" && contains name "append"
    | ConceptData.theorem name _ _ _ _ => 
      contains name "map" && contains name "append"
    | _ => false
    
  if mapAppendConcepts.length >= 2 then
    IO.println s!"[INDUCTION] Found {mapAppendConcepts.length} map-append patterns, generating inductive theorem!"
    newConcepts := newConcepts ++ [
      ConceptData.conjecture "map_append_inductive" (mkConst ``True) 0.95 {
        name := "map_append_inductive"
        created := 0
        parent := none
        interestingness := 0.95
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "induction_discovery"
      }
    ]
    IO.println s!"[INDUCTION] Generated high-priority map-append inductive conjecture!"
  
  -- Strategy 6: Detect list operation patterns in general
  let listOpConcepts := concepts.filter fun c => match c with
    | ConceptData.conjecture name _ _ _ => 
      contains name "list" || contains name "List" || contains name "nil" || contains name "cons"
    | ConceptData.theorem name _ _ _ _ => 
      contains name "list" || contains name "List" || contains name "nil" || contains name "cons"
    | _ => false
    
  if listOpConcepts.length >= 5 then
    IO.println s!"[INDUCTION] Found {listOpConcepts.length} list operation concepts, generating general list inductive principles!"
    newConcepts := newConcepts ++ [
      ConceptData.conjecture "general_list_induction_principle" (mkConst ``True) 0.90 {
        name := "general_list_induction_principle"
        created := 0
        parent := none
        interestingness := 0.90
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "induction_discovery"
      }
    ]
  
  IO.println s!"[INDUCTION] Generated {newConcepts.length} inductive concepts"
  return newConcepts


end LeanDisco