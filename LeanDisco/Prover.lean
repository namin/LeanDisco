import LeanDisco.Types
import LeanDisco.SimpleTactics
import Lean.Elab.Tactic.Induction
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Simp

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab Tactic

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
        let suitableTerms ← concepts.filterMapM fun c => match c with
          | ConceptData.definition name typ defValue _ _ metadata =>
            if metadata.generationMethod == "seed" || metadata.generationMethod == "mined" then do
              -- Proper type checking using isDefEq
              let defType ← inferType defValue
              if ← isDefEq defType varType then
                return some (name, defValue)
              else
                return none
            else
              return none
          | _ => return none

        for (termName, termValue) in suitableTerms.take 3 do
          let specName := s!"{conjName}_spec_{termName}"
          if !concepts.any (fun c => getConceptName c == specName) then
            -- Instantiate the body with the actual term value
            let instantiatedBody := body.instantiate1 termValue
            let isValid ← isWellFormedConjecture instantiatedBody
            if isValid then
              newConcepts := newConcepts ++ [
                ConceptData.conjecture specName instantiatedBody (evidence * 0.8) {
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

/-- General helper functions for theorem construction -/

-- Helper to create forall expressions
def mkForallExpr (varName : String) (varType : Expr) (body : Expr) : Expr :=
  Expr.forallE (Name.mkSimple varName) varType body (BinderInfo.default)

-- Helper to create equality expressions
def mkEqualityExpr (left : Expr) (right : Expr) (type : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) type left right

/-- Generic induction structure detection - delegates to domain-specific patterns -/
def detectInductiveStructure (concepts : List ConceptData) : MetaM (List (String × Bool × List Expr)) := do
  let mut inductiveStructures : List (String × Bool × List Expr) := []
  
  for concept in concepts do
    match concept with
    | ConceptData.definition name _ expr _ _ metadata => do
      -- Check if this is explicitly marked as a base case or inductive step
      if contains name "base_case" || contains metadata.generationMethod "base" then
        inductiveStructures := (name, true, [expr]) :: inductiveStructures
      else if contains name "inductive_step" || contains metadata.generationMethod "inductive" then
        inductiveStructures := (name, false, [expr]) :: inductiveStructures
      -- Generic patterns for foundational/atomic concepts (likely base cases)
      else if metadata.specializationDepth == 0 && metadata.generationMethod == "seed" then
        inductiveStructures := (name, true, [expr]) :: inductiveStructures
    | ConceptData.conjecture name _ _ metadata => do
      -- Check for explicit base case patterns
      if contains name "base_case" || contains metadata.generationMethod "base" then
        inductiveStructures := (name, true, []) :: inductiveStructures
      -- Check for explicit inductive step patterns
      else if contains name "inductive_step" || contains metadata.generationMethod "inductive" then
        inductiveStructures := (name, false, []) :: inductiveStructures
    | _ => pure ()
  
  return inductiveStructures

/-- Generic analysis of expression suitability for inductive reasoning -/
def isInductiveCandidate (expr : Expr) : MetaM Bool := do
  -- Generic check: look for complex expressions that might benefit from induction
  let hasComplexStructure := expr.find? fun e =>
    match e with
    | Expr.app _ _ => true  -- Function applications might be recursive
    | Expr.forallE _ _ _ _ => true  -- Universal quantification suggests induction potential
    | _ => false
  
  return hasComplexStructure.isSome

/-- Generate well-formed inductive hypothesis -/
def generateInductiveHypothesis (basePattern : String) (concepts : List ConceptData) : MetaM (Option Expr) := do
  -- Look for related concepts to form an inductive hypothesis
  let relatedConcepts := concepts.filter fun c =>
    let name := getConceptName c
    contains name basePattern
  
  if relatedConcepts.length >= 2 then
    -- Generate a simple universal quantification as an inductive hypothesis
    let hypName := s!"inductive_hyp_{basePattern}"
    IO.println s!"[INDUCTION] Generated hypothesis for pattern: {basePattern}"
    return some (mkConst ``True) -- Placeholder
  else
    return none

/-- Generic identification of base cases - looks for explicitly marked base cases -/
def identifyBaseCases (concepts : List ConceptData) : MetaM (List ConceptData) := do
  let baseCases := concepts.filter fun c =>
    match c with
    | ConceptData.definition name _ _ _ _ metadata => 
      contains name "base_case" || contains metadata.generationMethod "base" ||
      (metadata.specializationDepth == 0 && metadata.generationMethod == "seed")
    | ConceptData.conjecture name _ _ metadata =>
      contains name "base_case" || contains metadata.generationMethod "base"
    | _ => false
  
  IO.println s!"[INDUCTION] Identified {baseCases.length} potential base cases"
  return baseCases

/-- Generic identification of inductive steps - looks for explicitly marked inductive steps -/
def identifyInductiveSteps (concepts : List ConceptData) : MetaM (List ConceptData) := do
  let inductiveSteps := concepts.filter fun c =>
    match c with
    | ConceptData.definition name _ _ _ _ metadata => 
      contains name "inductive_step" || contains metadata.generationMethod "inductive"
    | ConceptData.conjecture name _ _ metadata =>
      contains name "inductive_step" || contains metadata.generationMethod "inductive"
    | _ => false
  
  IO.println s!"[INDUCTION] Identified {inductiveSteps.length} potential inductive steps"
  return inductiveSteps


/-- Group conjectures by common patterns in their names -/
def groupConjecturesByPattern (concepts : List ConceptData) : List (String × List ConceptData) :=
  let conjectures := concepts.filter fun c => 
    match c with | ConceptData.conjecture _ _ _ _ => true | _ => false
  
  -- Extract patterns from conjecture names
  let commonPatterns := ["length", "append", "reverse", "map", "filter", "fold"]
  
  commonPatterns.filterMap fun pattern =>
    let matchingConjectures := conjectures.filter fun c =>
      contains (getConceptName c) pattern
    if matchingConjectures.length > 0 then
      some (pattern, matchingConjectures)
    else
      none

/-- Generic theorem statement creation - provides generic inductive patterns -/
def createInductiveTheoremStatement (pattern : String) (conjectures : List ConceptData) : MetaM Expr := do
  -- For now, create generic inductive theorem patterns
  -- This will be replaced by a proper plugin system where domains register their generators
  IO.println s!"[INDUCTION] Creating generic theorem statement for pattern: {pattern}"
  
  -- Create meaningful theorem statements based on the pattern
  match pattern with
  | "length_append" => do
    -- ∀ l1 l2 : List α, length (l1 ++ l2) = length l1 + length l2
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l1") listType fun l1Var => do
    withLocalDeclD (Name.mkSimple "l2") listType fun l2Var => do
      -- length(l1 ++ l2)
      let natType := mkConst ``Nat
      let append := mkApp3 (mkConst ``List.append [levelZero]) natType l1Var l2Var
      let leftSide := mkApp2 (mkConst ``List.length [levelZero]) natType append
      
      -- length(l1) + length(l2)
      let len1 := mkApp2 (mkConst ``List.length [levelZero]) natType l1Var
      let len2 := mkApp2 (mkConst ``List.length [levelZero]) natType l2Var
      let rightSide := mkApp2 (mkConst ``Nat.add) len1 len2
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide (mkConst ``Nat)
      let forallL2 := mkForallExpr "l2" listType equality
      let forallL1 := mkForallExpr "l1" listType forallL2
      
      return forallL1
      
  | "reverse" => do
    -- ∀ l : List α, reverse (reverse l) = l
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l") listType fun lVar => do
      let natType := mkConst ``Nat
      let reverseOnce := mkApp2 (mkConst ``List.reverse [levelZero]) natType lVar
      let reverseTwice := mkApp2 (mkConst ``List.reverse [levelZero]) natType reverseOnce
      let equality := mkEqualityExpr reverseTwice lVar listType
      return mkForallExpr "l" listType equality
      
  | "append" => do
    -- ∀ l1 l2 l3 : List α, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l1") listType fun l1Var => do
    withLocalDeclD (Name.mkSimple "l2") listType fun l2Var => do
    withLocalDeclD (Name.mkSimple "l3") listType fun l3Var => do
      let natType := mkConst ``Nat
      let leftAppend := mkApp3 (mkConst ``List.append [levelZero]) natType l1Var l2Var
      let leftSide := mkApp3 (mkConst ``List.append [levelZero]) natType leftAppend l3Var
      
      let rightAppend := mkApp3 (mkConst ``List.append [levelZero]) natType l2Var l3Var
      let rightSide := mkApp3 (mkConst ``List.append [levelZero]) natType l1Var rightAppend
      
      let equality := mkEqualityExpr leftSide rightSide listType
      let forallL3 := mkForallExpr "l3" listType equality
      let forallL2 := mkForallExpr "l2" listType forallL3
      let forallL1 := mkForallExpr "l1" listType forallL2
      
      return forallL1
      
  | "length" => do
    -- ∀ l : List α, length (reverse l) = length l
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l") listType fun lVar => do
      let natType := mkConst ``Nat
      let reversedList := mkApp2 (mkConst ``List.reverse [levelZero]) natType lVar
      let leftSide := mkApp2 (mkConst ``List.length [levelZero]) natType reversedList
      let rightSide := mkApp2 (mkConst ``List.length [levelZero]) natType lVar
      let equality := mkEqualityExpr leftSide rightSide (mkConst ``Nat)
      return mkForallExpr "l" listType equality
      
  | _ => do
    -- Generic fallback for unknown patterns - create a simple property
    IO.println s!"[INDUCTION] Unknown pattern {pattern}, creating generic statement"
    let natType := mkConst ``Nat
    let body := mkEqualityExpr (mkConst ``Nat.zero) (mkConst ``Nat.zero) natType
    return mkForallExpr s!"{pattern}_x" natType body

/-- Generate an inductive theorem from a pattern of conjectures -/
def generateInductiveTheoremFromPattern (pattern : String) (conjectures : List ConceptData) 
    (baseCases : List ConceptData) : MetaM (Option ConceptData) := do
  
  -- For now, create a conjecture that expresses the inductive property generically
  let theoremName := s!"inductive_theorem_{pattern}"
  
  -- Check if we already have this theorem
  let existingNames := conjectures.map getConceptName
  if existingNames.any (fun name => name == theoremName) then
    return none
  
  -- Generate a meaningful theorem statement based on the pattern
  let theoremStatement ← createInductiveTheoremStatement pattern conjectures
  
  let newTheorem := ConceptData.conjecture theoremName theoremStatement 0.85 {
    name := theoremName
    created := 0
    parent := none
    interestingness := 0.90
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "induction_discovery"
  }
  
  return some newTheorem

/-- Generate concepts that provide guidance for proof structure -/
def generateProofStructureGuidance (baseCases inductiveSteps : List ConceptData) : MetaM (List ConceptData) := do
  let mut guidanceConcepts : List ConceptData := []
  
  -- Create a proof strategy concept
  let proofStrategy := ConceptData.heuristicRef "induction_proof_strategy" 
    "Strategy: Prove base case, then prove inductive step" {
    name := "induction_proof_strategy"
    created := 0
    parent := none
    interestingness := 0.80
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "induction_discovery"
  }
  
  guidanceConcepts := [proofStrategy]
  
  return guidanceConcepts

/-- Check if a goal type looks like something we might be able to prove -/
def isLikelyProvable (goalType : Expr) : Bool :=
  -- Very simple heuristic: check for equalities and universal quantification
  match goalType with
  | Expr.forallE _ _ body _ => isLikelyProvable body
  | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) _ ) _ => true  -- Equality
  | Expr.const ``True _ => true  -- Trivially true
  | _ => false

/-- Check if a type is inductive (List, Nat, etc.) -/
def isInductiveType (type : Expr) : Bool :=
  match type with
  | Expr.const ``Nat _ => true
  | Expr.app (Expr.const ``List _) _ => true
  | Expr.app (Expr.const ``Array _) _ => true
  | _ => false


/-- Helper functions for pattern matching -/
def isLengthOfEmptyList (expr : Expr) : Bool :=
  match expr with
  | Expr.app (Expr.const ``List.length _) arg => arg.isAppOf ``List.nil
  | _ => false

def isLengthOfAppend (expr : Expr) : Bool :=
  match expr with
  | Expr.app (Expr.const ``List.length _) arg => arg.isAppOf ``List.append
  | _ => false

def isAppendWithEmptyList (expr : Expr) : Bool :=
  match expr with
  | Expr.app (Expr.app (Expr.const ``List.append _) arg1) arg2 =>
    arg1.isAppOf ``List.nil || arg2.isAppOf ``List.nil
  | _ => false

def isAppendAssocPattern (lhs rhs : Expr) : Bool :=
  -- This is a simplified check - a full implementation would do deeper pattern matching
  match lhs.find? (fun e => e.isConstOf ``List.append), rhs.find? (fun e => e.isConstOf ``List.append) with
  | some _, some _ => true
  | _, _ => false

def isReverseOfEmptyList (expr : Expr) : Bool :=
  match expr with
  | Expr.app (Expr.const ``List.reverse _) arg => arg.isAppOf ``List.nil
  | _ => false

def isReverseReverse (expr : Expr) : Bool :=
  match expr with
  | Expr.app (Expr.const ``List.reverse _) inner =>
    inner.isAppOf ``List.reverse
  | _ => false

def containsEmptyList (expr : Expr) : Bool :=
  expr.find? (fun e => e.isAppOf ``List.nil) |>.isSome

/-- Check if expression contains List.length -/
def containsListLength (expr : Expr) : Bool :=
  expr.find? (fun e => e.isConstOf ``List.length) |>.isSome

/-- Check if expression contains List.append -/
def containsListAppend (expr : Expr) : Bool :=
  expr.find? (fun e => e.isConstOf ``List.append) |>.isSome

/-- Check if expression contains List.reverse -/
def containsListReverse (expr : Expr) : Bool :=
  expr.find? (fun e => e.isConstOf ``List.reverse) |>.isSome

/-- Try definitional unfolding for equality goals -/
def tryDefinitionalUnfolding (goalMVar : MVarId) (lhs rhs : Expr) : MetaM Bool := do
  try
    goalMVar.withContext do
      -- Try to unfold definitions and check if they become equal
      let lhsWhnf ← whnf lhs
      let rhsWhnf ← whnf rhs
      
      if lhsWhnf == rhsWhnf then
        let _ ← goalMVar.refl
        return true
      else
        -- Try using isDefEq for more sophisticated definitional equality
        let isEqual ← isDefEq lhsWhnf rhsWhnf
        if isEqual then
          let _ ← goalMVar.refl
          return true
        else
          return false
  catch _ =>
    return false

/-- Try tactics for base cases (empty lists, zero, etc.) -/
def tryBaseCaseTactics (goalMVar : MVarId) (goalType : Expr) : MetaM Bool := do
  try
    goalMVar.withContext do
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Pattern: f [] = something simple
        if containsEmptyList lhs then
          -- Try common base case lemmas
          let baseCaseLemmas := [
            ``List.length_nil, ``List.reverse_nil, ``List.append_nil,
            ``List.nil_append, ``Nat.zero_add, ``Nat.add_zero
          ]
          
          for lemma in baseCaseLemmas do
            try
              let _ ← goalMVar.apply (mkConst lemma)
              IO.println s!"[TACTICS] ✓ Solved with {lemma}"
              return true
            catch _ => pure ()
      | _ => pure ()
      
      return false
  catch _ =>
    return false

/-- Try tactics specific to List.length -/
def tryListLengthTactics (goalMVar : MVarId) (goalType : Expr) : MetaM Bool := do
  try
    goalMVar.withContext do
      -- Look for patterns like length [] = 0
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Check if lhs is length of empty list
        if isLengthOfEmptyList lhs && rhs.isConstOf ``Nat.zero then
          -- Apply List.length_nil
          try
            let _ ← goalMVar.apply (mkConst ``List.length_nil)
            IO.println s!"[TACTICS] ✓ Solved with List.length_nil"
            return true
          catch _ => pure ()
        
        -- Check for length append patterns
        if isLengthOfAppend lhs then
          try
            let _ ← goalMVar.apply (mkConst ``List.length_append)
            IO.println s!"[TACTICS] ✓ Solved with List.length_append"
            return true
          catch _ => pure ()
      | _ => pure ()
      
      return false
  catch _ =>
    return false

/-- Try tactics specific to List.append -/
def tryListAppendTactics (goalMVar : MVarId) (goalType : Expr) : MetaM Bool := do
  try
    goalMVar.withContext do
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Check for append with empty list patterns
        if isAppendWithEmptyList lhs then
          try
            let _ ← goalMVar.apply (mkConst ``List.nil_append)
            IO.println s!"[TACTICS] ✓ Solved with List.nil_append"
            return true
          catch _ =>
            try
              let _ ← goalMVar.apply (mkConst ``List.append_nil)
              IO.println s!"[TACTICS] ✓ Solved with List.append_nil"
              return true
            catch _ => pure ()
        
        -- Check for associativity patterns
        if isAppendAssocPattern lhs rhs then
          try
            let _ ← goalMVar.apply (mkConst ``List.append_assoc)
            IO.println s!"[TACTICS] ✓ Solved with List.append_assoc"
            return true
          catch _ => pure ()
      | _ => pure ()
      
      return false
  catch _ =>
    return false

/-- Try tactics specific to List.reverse -/
def tryListReverseTactics (goalMVar : MVarId) (goalType : Expr) : MetaM Bool := do
  try
    goalMVar.withContext do
      match goalType with
      | Expr.app (Expr.app (Expr.app (Expr.const ``Eq _) _) lhs) rhs =>
        -- Check for reverse of empty list
        if isReverseOfEmptyList lhs && rhs.isAppOf ``List.nil then
          try
            let _ ← goalMVar.apply (mkConst ``List.reverse_nil)
            IO.println s!"[TACTICS] ✓ Solved with List.reverse_nil"
            return true
          catch _ => pure ()
        
        -- Check for reverse reverse pattern
        if isReverseReverse lhs then
          try
            let _ ← goalMVar.apply (mkConst ``List.reverse_reverse)
            IO.println s!"[TACTICS] ✓ Solved with List.reverse_reverse"
            return true
          catch _ => pure ()
      | _ => pure ()
      
      return false
  catch _ =>
    return false

/-- Try specialized tactics for common mathematical patterns -/
def trySpecializedTactics (goalMVar : MVarId) (goalType : Expr) : MetaM Bool := do
  try
    -- Handle List.length patterns
    if containsListLength goalType then
      let solved ← tryListLengthTactics goalMVar goalType
      if solved then return true
    
    -- Handle List.append patterns
    if containsListAppend goalType then
      let solved ← tryListAppendTactics goalMVar goalType
      if solved then return true
    
    -- Handle List.reverse patterns
    if containsListReverse goalType then
      let solved ← tryListReverseTactics goalMVar goalType
      if solved then return true
    
    -- Handle base case patterns (empty list, zero)
    let solved ← tryBaseCaseTactics goalMVar goalType
    if solved then return true
    
    return false
  catch _ =>
    return false

/-- Try enhanced tactics for solving induction subgoals using the simple tactic system -/
def tryBasicTactics (goalMVar : MVarId) : MetaM Bool := do
  try
    let goalType ← goalMVar.getType
    IO.println s!"[TACTICS] Trying to solve: {goalType}"
    
    -- Use the simple tactic system
    let tactics := getSimpleTactics
    let solved ← trySimpleTactics tactics goalMVar
    if solved then
      IO.println s!"[TACTICS] ✓ Solved with simple tactics"
      return true
    
    -- Fallback: try some legacy specialized tactics if the simple tactics didn't work
    let legacySolved ← trySpecializedTactics goalMVar goalType
    if legacySolved then
      IO.println s!"[TACTICS] ✓ Solved with legacy tactics"
      return true
    
    IO.println s!"[TACTICS] ✗ Could not solve goal"
    return false
  catch e =>
    IO.println s!"[TACTICS] Error in tactics: {← e.toMessageData.toString}"
    return false


/-- Apply real Lean induction tactic to a goal -/
def applyInductionTactic (goalMVar : MVarId) (varName : Name) (varType : Expr) : MetaM Bool := do
  try
    IO.println s!"[INDUCTION] Attempting real induction on variable {varName}"
    
    -- We need to find the FVarId for the variable name within the goal context
    let goalType ← goalMVar.getType
    goalMVar.withContext do
      let localCtx ← getLCtx
      let fvarId? := localCtx.findFromUserName? varName
      
      match fvarId? with
      | some localDecl => do
        let fvarId := localDecl.fvarId
        IO.println s!"[INDUCTION] Found variable {varName} as FVar, applying real induction"
        
        try
          -- Use Lean's actual induction tactic
          IO.println s!"[INDUCTION] Calling MVarId.induction on {varName} of type {varType}"
          
          -- Apply induction using Lean's built-in induction
          -- Get the recursor name for the inductive type
          let inductType ← inferType (mkFVar fvarId)
          let recursorName? := match inductType with
            | Expr.const name _ => some (name.str "rec")
            | Expr.app (Expr.const name _) _ => some (name.str "rec")
            | _ => none
          
          match recursorName? with
          | some recursorName => do
            let inductionResult ← goalMVar.induction fvarId recursorName
            
            IO.println s!"[INDUCTION] Induction generated {inductionResult.size} subgoals"
            
            -- Try to solve each subgoal generated by induction
            let mut allSolved := true
            for i in [0:inductionResult.size] do
              let inductionCase := inductionResult[i]!
              IO.println s!"[INDUCTION] Solving subgoal {i + 1}/{inductionResult.size}"
              
              -- For the base case (i == 0), we need to handle it specially
              let solved ← if i == 0 then
                -- Base case: try to instantiate metavariables and solve
                inductionCase.mvarId.withContext do
                  let goalType ← inductionCase.mvarId.getType
                  IO.println s!"[INDUCTION] Base case goal: {goalType}"
                  
                  -- Try to instantiate any remaining metavariables with the base case value
                  let instantiated ← instantiateMVars goalType
                  if instantiated != goalType then
                    IO.println s!"[INDUCTION] Instantiated goal: {instantiated}"
                  
                  tryBasicTactics inductionCase.mvarId
              else
                -- Inductive case: use the inductive hypothesis
                tryBasicTactics inductionCase.mvarId
                
              if !solved then
                allSolved := false
                IO.println s!"[INDUCTION] ✗ Failed to solve subgoal {i + 1}"
              else
                IO.println s!"[INDUCTION] ✓ Solved subgoal {i + 1}"
            
            if allSolved then
              IO.println s!"[INDUCTION] ✓ Successfully completed real induction proof!"
            else
              IO.println s!"[INDUCTION] ✗ Induction generated subgoals but couldn't solve them all"
            
            return allSolved
          | none => do
            IO.println s!"[INDUCTION] Could not determine recursor for type {inductType}"
            return false
          
        catch e =>
          IO.println s!"[INDUCTION] Real induction tactic failed: {← e.toMessageData.toString}"
          -- Fallback: try to solve the goal directly with basic tactics
          let solved ← tryBasicTactics goalMVar
          return solved
          
      | none => do
        IO.println s!"[INDUCTION] Could not find variable {varName} in goal context"
        return false
      
  catch e =>
    IO.println s!"[INDUCTION] Error applying induction tactic: {← e.toMessageData.toString}"
    return false

/-- Attempt to prove a goal by induction -/
def attemptInductionProof (goalMVar : MVarId) (goalType : Expr) : MetaM Bool := do
  try
    IO.println s!"[INDUCTION] Attempting induction on goal type: {goalType}"
    
    -- First, we need to introduce quantified variables using the intro tactic
    let goalAfterIntros ← goalMVar.intros
    let (introducedVars, newGoal) := goalAfterIntros
    
    if introducedVars.size > 0 then
      IO.println s!"[INDUCTION] Introduced {introducedVars.size} variables"
      
      -- Look for inductive variables among the introduced ones
      newGoal.withContext do
        let localCtx ← getLCtx
        for fvarId in introducedVars do
          let localDecl := localCtx.get! fvarId
          let varName := localDecl.userName
          let varType ← inferType (mkFVar fvarId)
          
          IO.println s!"[INDUCTION] Checking introduced variable {varName} of type {varType}"
          
          -- Check if this variable has an inductive type
          if isInductiveType varType then
            IO.println s!"[INDUCTION] Variable {varName} has inductive type {varType}, applying induction"
            
            -- Apply induction on this variable
            let result ← applyInductionTactic newGoal varName varType
            return result
        
        -- If no inductive variables found, try basic tactics on the simplified goal
        IO.println s!"[INDUCTION] No inductive variables found, trying basic tactics"
        let result ← tryBasicTactics newGoal
        return result
    else
      IO.println s!"[INDUCTION] No variables to introduce, trying basic tactics directly"
      let result ← tryBasicTactics goalMVar
      return result
      
  catch e =>
    IO.println s!"[INDUCTION] Error during induction attempt"
    return false


/-- Try a simple proof attempt using basic tactics -/
def trySimpleProofAttempt (goalMVar : MVarId) (statement : Expr) : MetaM Bool := do
  try
    IO.println s!"[INDUCTION] Attempting real proof by induction"
    
    let goalType ← goalMVar.getType
    IO.println s!"[INDUCTION] Goal type: {goalType}"
    
    -- Try to identify the inductive structure and apply induction
    let success ← attemptInductionProof goalMVar goalType
    if success then
      IO.println s!"[INDUCTION] ✓ Successfully proved by induction!"
      return true
    
    -- If induction fails, try basic tactics as fallback
    let basicSuccess ← tryBasicTactics goalMVar
    if basicSuccess then
      IO.println s!"[INDUCTION] ✓ Solved with basic tactics!"
      return true
    
    IO.println s!"[INDUCTION] Could not prove goal"
    return false
      
  catch e =>
    IO.println s!"[INDUCTION] Error during proof attempt"
    return false

/-- Actually attempt to prove a theorem by induction using Lean tactics -/
def attemptRealInductiveProof (theoremName : String) (statement : Expr) : MetaM (Option ConceptData) := do
  IO.println s!"[INDUCTION] Attempting REAL proof by induction: {theoremName}"
  
  try
    -- Create a proper proof goal and attempt to prove it
    let result ← withNewMCtxDepth do
      let goalType := statement
      let goal ← mkFreshExprMVar goalType
      
      IO.println s!"[INDUCTION] Created goal for {theoremName}"
      
      -- Try to prove the goal using real Lean tactics
      let success ← trySimpleProofAttempt goal.mvarId! statement
      
      if success = true then
        IO.println s!"[INDUCTION] ✓ Successfully proved {theoremName} by induction!"
        
        -- Get the actual proof term
        let proof ← instantiateMVars goal
        
        return some (ConceptData.theorem theoremName statement proof [] {
          name := theoremName
          created := 0
          parent := none
          interestingness := 1.0  -- High value for actually proved theorems
          useCount := 0
          successCount := 1
          specializationDepth := 0
          generationMethod := "real_induction_proof"
        })
      else
        IO.println s!"[INDUCTION] ✗ Failed to prove {theoremName} by induction"
        return none
    
    return result
  catch e =>
    IO.println s!"[INDUCTION] Error during real proof attempt for {theoremName}"
    return none



/-- Find inductive structure in a statement -/
def findInductiveStructure (statement : Expr) : MetaM (Option Name × Option Name) := do
  -- Look for forall quantification over List or Nat
  match statement with
  | Expr.forallE varName varType body _ =>
    -- Check if varType is an inductive type we can handle
    match varType with
    | Expr.app (Expr.const typeName _) _ =>
      if typeName == ``List then
        return (some ``List, some varName)
      else if typeName == ``Nat then  
        return (some ``Nat, some varName)
      else
        return (none, none)
    | Expr.const typeName _ =>
      if typeName == ``Nat then
        return (some ``Nat, some varName)
      else
        return (none, none)
    | _ => return (none, none)
  | _ => return (none, none)


/-- Generate theorem about operation composition - delegates to domain-specific generators -/
def generateOperationCompositionTheorem (op1 op2 : String) : MetaM (Option (String × Expr)) := do
  try
    -- Check if this is a List operation and delegate to List domain
    if contains op1 "List." || contains op2 "List." then
      -- Generate generic composition theorems (domain plugins would handle specifics)
      if (contains op1 "length" && contains op2 "append") then
        let theoremName := "length_append_distributive"
        let statement ← createInductiveTheoremStatement "length_append" []
        IO.println s!"[INDUCTION] Generated generic composition theorem: {theoremName}"
        return some (theoremName, statement)
      else if (contains op1 "append" && contains op2 "append") then
        let theoremName := "append_associative" 
        let statement ← createInductiveTheoremStatement "append" []
        IO.println s!"[INDUCTION] Generated generic composition theorem: {theoremName}"
        return some (theoremName, statement)
      else
        return none
    else
      -- Generic case for other domains - for now just skip to avoid placeholders
      return none
  catch e =>
    return none

/-- Generate theorem about self-inverse operations - delegates to domain-specific generators -/
def generateSelfInverseTheorem (op : String) : MetaM (Option (String × Expr)) := do
  try
    -- Check if this is a List operation and delegate to List domain
    if contains op "List." then
      -- Generate generic self-inverse theorems (domain plugins would handle specifics)
      if contains op "reverse" then
        let theoremName := "reverse_involutive"
        let statement ← createInductiveTheoremStatement "reverse" []
        IO.println s!"[INDUCTION] Generated generic involution theorem: {theoremName}"
        return some (theoremName, statement)
      else if contains op "append" then
        let theoremName := "append_associative"
        let statement ← createInductiveTheoremStatement "append" []
        IO.println s!"[INDUCTION] Generated generic associativity theorem: {theoremName}"
        return some (theoremName, statement)
      else if contains op "length" then
        let theoremName := "length_append"
        let statement ← createInductiveTheoremStatement "length" []
        IO.println s!"[INDUCTION] Generated generic length theorem: {theoremName}"
        return some (theoremName, statement)
      else
        return none
    else
      -- Generic case for other domains - for now just skip to avoid placeholders
      return none
  catch e =>
    return none

/-- Discover candidate inductive theorems from domain operations -/
def discoverInductiveTheoremCandidates (concepts : List ConceptData) : MetaM (List (String × Expr)) := do
  let mut candidates : List (String × Expr) := []
  
  -- Find operations that work on inductive types
  let operations := concepts.filterMap fun c => 
    match c with
    | ConceptData.heuristicRef name _ _ => 
      if contains name "List." || contains name "Nat." then
        some name
      else none
    | _ => none
  
  IO.println s!"[INDUCTION] Found {operations.length} operations on inductive types"
  
  -- Generate theorem candidates for common patterns
  for op1 in operations do
    for op2 in operations do
      if op1 != op2 then
        -- Try to generate theorems about operation composition
        let candidateTheorem ← generateOperationCompositionTheorem op1 op2
        match candidateTheorem with
        | some (name, expr) => 
          candidates := (name, expr) :: candidates
          IO.println s!"[INDUCTION] Generated candidate: {name}"
        | none => pure ()
  
  -- Generate single-operation theorems (like reverse(reverse(x)) = x)
  for op in operations do
    let candidateTheorem ← generateSelfInverseTheorem op
    match candidateTheorem with
    | some (name, expr) => 
      candidates := (name, expr) :: candidates
      IO.println s!"[INDUCTION] Generated self-inverse candidate: {name}"
    | none => pure ()
  
  return candidates


/-- Attempt to prove a discovered theorem candidate -/
def attemptProveCandidate (name : String) (statement : Expr) : MetaM (Option ConceptData) := do
  IO.println s!"[INDUCTION] Attempting to prove discovered candidate: {name}"
  
  -- Use the real proof attempt function
  let result ← attemptRealInductiveProof name statement
  
  match result with
  | some thm =>
    IO.println s!"[INDUCTION] ✓ Successfully proved discovered theorem: {name}"
    return some thm
  | none =>
    IO.println s!"[INDUCTION] ✗ Could not prove {name}, but discovered interesting conjecture"
    -- Still valuable as a conjecture
    let conjecture := ConceptData.conjecture name statement 0.75 {
      name := name
      created := 0
      parent := none
      interestingness := 0.80
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "discovered_induction_conjecture"
    }
    return some conjecture

/-- Improved induction heuristic that actually attempts proofs -/
def inductionHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  IO.println s!"[INDUCTION] Starting real inductive reasoning on {concepts.length} concepts..."
  
  -- Strategy 1: Discover theorem candidates from domain operations
  let candidates ← discoverInductiveTheoremCandidates concepts
  IO.println s!"[INDUCTION] Discovered {candidates.length} theorem candidates"
  
  -- Strategy 2: Attempt to prove each candidate
  for (name, statement) in candidates do
    let result ← attemptProveCandidate name statement
    match result with
    | some concept =>
      newConcepts := concept :: newConcepts
    | none => pure ()
  
  -- Strategy 3: Only add proof guidance if we have real theorems
  let successfulProofs := newConcepts.filter fun c =>
    match c with
    | ConceptData.theorem _ _ _ _ metadata => metadata.generationMethod == "real_induction_proof"
    | _ => false
  
  if successfulProofs.length > 0 then
    let proofGuide := ConceptData.heuristicRef "induction_success_guide" 
      s!"Successfully proved {successfulProofs.length} theorems by induction" {
      name := "induction_success_guide"
      created := 0
      parent := none
      interestingness := 0.90
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "induction_discovery"
    }
    newConcepts := proofGuide :: newConcepts
  
  let provedCount := successfulProofs.length
  let conjectureCount := newConcepts.length - successfulProofs.length - (if successfulProofs.length > 0 then 1 else 0)
  
  IO.println s!"[INDUCTION] RESULTS: {provedCount} theorems proved, {conjectureCount} conjectures discovered"
  return newConcepts


end LeanDisco