-- This module serves as the root of the `LeanDisco` library.
-- Import modules here that should be built as part of the library.
import LeanDisco.Basic

import Lean
import Lean.Meta.Basic
import Lean.Elab.Command

 -- for mining!
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab

/-
# Eurisko-Inspired Discovery System for Lean

This system represents mathematical concepts, heuristics, and discovery tasks
as first-class objects in Lean, enabling automated mathematical discovery
with formal verification.
-/

namespace LeanDisco

/-- Configuration for controlling discovery -/
structure DiscoveryConfig where
  maxSpecializationDepth : Nat := 4
  maxConceptsPerIteration : Nat := 1000
  pruneThreshold : Float := 0.1
  deduplicateConcepts : Bool := true
  canonicalizeConcepts : Bool := true
  filterInternalProofs : Bool := true
  enableConjectures : Bool := true
  enablePatternRecognition : Bool := true

/-- Metadata for tracking concept performance and history -/
structure ConceptMetadata where
  name : String
  created : Nat
  parent : Option String
  interestingness : Float
  useCount : Nat
  successCount : Nat
  specializationDepth : Nat := 0
  generationMethod : String := "unknown"
  deriving Repr, BEq

/-- Core concept data with dependencies -/
inductive ConceptData where
  | definition :
    (name : String) →
    (type : Expr) →
    (value : Expr) →
    (canonicalValue : Option Expr) →
    (dependencies : List String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | theorem :
    (name : String) →
    (statement : Expr) →
    (proof : Expr) →
    (dependencies : List String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | conjecture :
    (name : String) →
    (statement : Expr) →
    (evidence : Float) →
    (metadata : ConceptMetadata) →
    ConceptData
  | pattern :
    (name : String) →
    (description : String) →
    (instances : List String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | heuristicRef :
    (name : String) →
    (description : String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | taskRef :
    (name : String) →
    (goal : String) →
    (metadata : ConceptMetadata) →
    ConceptData

/-- Unique identifier for concepts -/
abbrev ConceptId := String

/-- Type for heuristic functions -/
abbrev HeuristicFn := DiscoveryConfig → List ConceptData → MetaM (List ConceptData)

/-- Type for evaluation functions -/
abbrev EvaluationFn := List ConceptData → MetaM Float

/-- Simple association list for storing heuristics -/
structure HeuristicRegistry where
  entries : List (ConceptId × HeuristicFn)

def HeuristicRegistry.empty : HeuristicRegistry := ⟨[]⟩

def HeuristicRegistry.insert (reg : HeuristicRegistry) (id : ConceptId) (fn : HeuristicFn) : HeuristicRegistry :=
  ⟨(id, fn) :: reg.entries⟩

def HeuristicRegistry.find? (reg : HeuristicRegistry) (id : ConceptId) : Option HeuristicFn :=
  reg.entries.lookup id

/-- Simple association list for storing evaluators -/
structure EvaluationRegistry where
  entries : List (ConceptId × EvaluationFn)

def EvaluationRegistry.empty : EvaluationRegistry := ⟨[]⟩

def EvaluationRegistry.insert (reg : EvaluationRegistry) (id : ConceptId) (fn : EvaluationFn) : EvaluationRegistry :=
  ⟨(id, fn) :: reg.entries⟩

def EvaluationRegistry.find? (reg : EvaluationRegistry) (id : ConceptId) : Option EvaluationFn :=
  reg.entries.lookup id

/-- Cache for previously attempted concept combinations -/
structure ConceptCache where
  attemptedApplications : List (String × String) := []  -- (function, argument) pairs
  attemptedSpecializations : List (String × String) := []  -- (theorem, value) pairs
  attemptedConjectures : List String := []  -- conjecture statements as strings
  normalizedExpressions : List (Expr × String) := []  -- (normalized expr, concept name) pairs

/-- Track failed proof attempts -/
structure FailedAttempt where
  statementStr : String
  attemptCount : Nat
  lastAttempt : Nat  -- iteration number

/-- Result of applying a heuristic or evolution step -/
structure Discovery where
  newConcepts : List ConceptData
  modifiedConcepts : List ConceptData
  explanation : String

/-- Knowledge base containing all discovered concepts -/
structure KnowledgeBase where
  concepts : List ConceptData
  recentConcepts : List ConceptData
  heuristics : HeuristicRegistry
  evaluators : EvaluationRegistry
  config : DiscoveryConfig
  iteration : Nat
  history : List (Nat × List String)
  cache : ConceptCache := {}
  failedProofs : List FailedAttempt := []

/-- Extract concept name -/
def getConceptName : ConceptData → String
  | ConceptData.definition n _ _ _ _ _ => n
  | ConceptData.theorem n _ _ _ _ => n
  | ConceptData.conjecture n _ _ _ => n
  | ConceptData.pattern n _ _ _ => n
  | ConceptData.heuristicRef n _ _ => n
  | ConceptData.taskRef n _ _ => n

/-- Get concept metadata -/
def getConceptMetadata : ConceptData → ConceptMetadata
  | ConceptData.definition _ _ _ _ _ m => m
  | ConceptData.theorem _ _ _ _ m => m
  | ConceptData.conjecture _ _ _ m => m
  | ConceptData.pattern _ _ _ m => m
  | ConceptData.heuristicRef _ _ m => m
  | ConceptData.taskRef _ _ m => m

/-- Update concept metadata -/
def updateConceptMetadata (c : ConceptData) (f : ConceptMetadata → ConceptMetadata) : ConceptData :=
  match c with
  | ConceptData.definition n t v cv d m => ConceptData.definition n t v cv d (f m)
  | ConceptData.theorem n s p d m => ConceptData.theorem n s p d (f m)
  | ConceptData.conjecture n s e m => ConceptData.conjecture n s e (f m)
  | ConceptData.pattern n d i m => ConceptData.pattern n d i (f m)
  | ConceptData.heuristicRef n d m => ConceptData.heuristicRef n d (f m)
  | ConceptData.taskRef n g m => ConceptData.taskRef n g (f m)

/-- Get concept value/statement -/
def getConceptExpr : ConceptData → Option Expr
  | ConceptData.definition _ _ v _ _ _ => some v
  | ConceptData.theorem _ s _ _ _ => some s
  | ConceptData.conjecture _ s _ _ => some s
  | _ => none

/-- Extract natural number literal from expression -/
partial def extractNatLiteral (e : Expr) : MetaM (Option Nat) := do
  let e' ← whnf e
  match e' with
  | .const ``Nat.zero _ => return some 0
  | .app (.const ``Nat.succ _) n => do
    if let some n' ← extractNatLiteral n then
      return some (n' + 1)
    else
      return none
  | _ => return none

/-- Generate the next natural number -/
def generateNextNumber (kb : KnowledgeBase) : MetaM (Option ConceptData) := do
  let existingNumbers := kb.concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "num_" then
        n.drop 4 |>.toNat?
      else if n == "zero" then some 0
      else if n == "one" then some 1
      else if n == "two" then some 2
      else none
    | _ => none

  let maxNum := existingNumbers.foldl max 0
  if maxNum < 10 then  -- Don't go too high
    let nextNum := maxNum + 1
    let numExpr := (List.range nextNum).foldl (fun acc _ =>
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)

    return some $ ConceptData.definition s!"num_{nextNum}"
      (mkConst ``Nat) numExpr none []
      { name := s!"num_{nextNum}"
        created := kb.iteration
        parent := none
        interestingness := 0.5
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "number_generation" }
  else
    return none

/-- Canonicalize a concept to its simplest form -/
def canonicalizeConcept (c : ConceptData) : MetaM ConceptData := do
  match c with
  | ConceptData.definition n t v cached deps meta =>
    if cached.isSome then
      return c  -- Already canonicalized
    else
      let v' ← reduce v  -- Use reduce instead of just whnf
      -- Check if it's a natural number
      if let some num ← extractNatLiteral v' then
        let newName := s!"num_{num}"
        return ConceptData.definition newName t v' (some v') deps
          { meta with name := newName }
      else
        return ConceptData.definition n t v' (some v') deps meta
  | _ => return c

/-- Check if a concept name indicates an internal proof term -/
def isInternalProofTerm (name : String) : Bool :=
  ((name.splitOn "._proof_").length > 1) || ((name.splitOn ".match_").length > 1)

/-- Check if two expressions are definitionally equal -/
def exprsEqual (e1 e2 : Expr) : MetaM Bool := do
  try
    isDefEq e1 e2
  catch _ => return false

/-- Enhanced deduplication that checks semantic equivalence more thoroughly -/
def deduplicateAgainstExisting (existing : List ConceptData) (newConcepts : List ConceptData) : MetaM (List ConceptData) := do
  let mut result : List ConceptData := []
  let mut duplicateCount := 0

  -- Build normalized expression cache from existing concepts
  let mut existingNormalized : List (Expr × String) := []
  for c in existing do
    if let some expr := getConceptExpr c then
      let normalized ← reduce expr
      existingNormalized := (normalized, getConceptName c) :: existingNormalized

  -- Check each new concept
  for c in newConcepts do
    if let some expr := getConceptExpr c then
      let normalized ← reduce expr
      let mut isDuplicate := false

      -- Check against existing concepts
      for (existingExpr, existingName) in existingNormalized do
        if ← exprsEqual normalized existingExpr then
          isDuplicate := true
          duplicateCount := duplicateCount + 1
          IO.println s!"[DEBUG] Duplicate found: {getConceptName c} duplicates {existingName}"
          break

      if !isDuplicate then
        result := c :: result
        -- Add to our normalized set for checking within this batch
        existingNormalized := (normalized, getConceptName c) :: existingNormalized
    else
      -- Keep non-expression concepts (heuristics, tasks, patterns)
      result := c :: result

  if duplicateCount > 0 then
    IO.println s!"[DEBUG] Removed {duplicateCount} duplicates out of {newConcepts.length} new concepts"

  return result.reverse

/-- Filter concepts by specialization depth -/
def filterByDepth (maxDepth : Nat) (concepts : List ConceptData) : List ConceptData :=
  concepts.filter fun c =>
    (getConceptMetadata c).specializationDepth ≤ maxDepth

/-- Filter out internal proof terms -/
def filterInternalTerms (concepts : List ConceptData) : List ConceptData :=
  concepts.filter fun c =>
    !isInternalProofTerm (getConceptName c)

/-- Apply all configured filters and cleanup -/
def cleanupConcepts (config : DiscoveryConfig) (existing : List ConceptData) (newConcepts : List ConceptData) : MetaM (List ConceptData) := do
  let mut cleaned := newConcepts

  -- Filter internal proof terms
  if config.filterInternalProofs then
    cleaned := filterInternalTerms cleaned

  -- Filter by depth
  cleaned := filterByDepth config.maxSpecializationDepth cleaned

  -- Canonicalize
  if config.canonicalizeConcepts then
    cleaned ← cleaned.mapM canonicalizeConcept

  -- Deduplicate against existing concepts
  if config.deduplicateConcepts then
    cleaned ← deduplicateAgainstExisting existing cleaned

  -- Special deduplication for patterns - check by name only
  let cleanedPatterns := cleaned.filter fun c => match c with
    | ConceptData.pattern name _ _ _ =>
      -- Just check if pattern name already exists
      !existing.any fun e => match e with
        | ConceptData.pattern ename _ _ _ => name == ename
        | _ => false
    | _ => true

  return cleanedPatterns

/-- Update concept's interestingness score -/
def updateConceptScore (c : ConceptData) (score : Float) : ConceptData :=
  match c with
  | ConceptData.definition n t v cached d m =>
      ConceptData.definition n t v cached d { m with interestingness := score }
  | ConceptData.theorem n s p d m =>
      ConceptData.theorem n s p d { m with interestingness := score }
  | ConceptData.conjecture n s e m =>
      ConceptData.conjecture n s e { m with interestingness := score }
  | ConceptData.pattern n d i m =>
      ConceptData.pattern n d i { m with interestingness := score }
  | ConceptData.heuristicRef n d m =>
      ConceptData.heuristicRef n d { m with interestingness := score }
  | ConceptData.taskRef n g m =>
      ConceptData.taskRef n g { m with interestingness := score }

/-- Verify a definition is type-correct -/
def verifyDefinition (type : Expr) (value : Expr) : MetaM Bool := do
  try
    let valueType ← inferType value
    isDefEq valueType type
  catch _ => return false

/-- Verify a theorem by checking its proof -/
def verifyTheorem (statement : Expr) (proof : Expr) : MetaM Bool := do
  try
    let proofType ← inferType proof
    isDefEq proofType statement
  catch _ => return false

/-- Calculate structural similarity between expressions -/
partial def structuralSimilarity (e1 e2 : Expr) : MetaM Float := do
  match (e1, e2) with
  | (.app f1 a1, .app f2 a2) =>
    let fSim ← structuralSimilarity f1 f2
    let aSim ← structuralSimilarity a1 a2
    return (fSim + aSim) / 2.0
  | (.const n1 _, .const n2 _) =>
    return if n1 == n2 then 1.0 else 0.0
  | (.forallE _ t1 b1 _, .forallE _ t2 b2 _) =>
    let tSim ← structuralSimilarity t1 t2
    let bSim ← structuralSimilarity b1 b2
    return (tSim + bSim) / 2.0
  | (.lam _ t1 b1 _, .lam _ t2 b2 _) =>
    let tSim ← structuralSimilarity t1 t2
    let bSim ← structuralSimilarity b1 b2
    return (tSim + bSim) / 2.0
  | _ =>
    if ← isDefEq e1 e2 then return 0.5
    else return 0.0

/-- Expression size helper -/
partial def exprSize : Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ _ b _ => 1 + exprSize b
  | .forallE _ _ b _ => 1 + exprSize b
  | .letE _ _ v b _ => 1 + exprSize v + exprSize b
  | .lit _ => 1
  | .mdata _ e => 1 + exprSize e
  | .proj _ _ e => 1 + exprSize e

/-- Calculate evidence based on structural similarity and known theorems -/
def calculateConjectureEvidence (stmt : Expr) (kb : KnowledgeBase) : MetaM Float := do
  let mut evidence := 0.1  -- Base evidence

  -- Check structural similarity to proven theorems
  let mut maxSimilarity := 0.0
  for c in kb.concepts do
    match c with
    | ConceptData.theorem _ thmStmt _ _ _ =>
      let similarity ← structuralSimilarity stmt thmStmt
      maxSimilarity := max maxSimilarity similarity
    | _ => pure ()

  evidence := evidence + maxSimilarity * 0.3

  -- Boost evidence for simpler statements
  let complexity := exprSize stmt
  evidence := evidence + (1.0 / (1.0 + complexity.toFloat / 10.0)) * 0.3

  return min 1.0 evidence

/-- Enhanced conjecture proving with more tactics -/
def tryProveConjecture (stmt : Expr) : MetaM (Option Expr) := do
  try
    -- Try reflexivity for equality statements
    match stmt with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
      if ← isDefEq lhs rhs then
        let proof ← mkAppM ``Eq.refl #[lhs]
        return some proof
      else
        -- Try reducing both sides
        let lhs' ← reduce lhs
        let rhs' ← reduce rhs
        if ← isDefEq lhs' rhs' then
          let proof ← mkAppM ``Eq.refl #[lhs']
          return some proof
        else
          return none
    | _ => return none
  catch _ => return none

/-- Check if a constant should be included based on filters -/
def shouldIncludeConstant (name : Name) (allowedPrefixes : List String) : Bool :=
  allowedPrefixes.any (·.isPrefixOf name.toString)

def shouldIncludeLib (env : Environment) (name : Name) (allowedLibs : List String) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx =>
      let modName := env.header.moduleNames[idx]!
      allowedLibs.any (·.isPrefixOf modName.toString)
  | none => false

/-- Mine concepts from the Lean environment -/
def mineEnvironment (allowedPrefixes : List String) (allowedLibs : List String) : MetaM (List ConceptData) := do
  let env ← getEnv
  let mut concepts := []

  let mkMeta (name : String) : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 0.5
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "mined"
  }

  for (name, info) in env.constants do
    if (shouldIncludeConstant name allowedPrefixes || shouldIncludeLib env name allowedLibs) && !isInternalProofTerm name.toString then
      match info with
      | .defnInfo val =>
        match val.safety with
        | .safe =>
          concepts := concepts ++ [ConceptData.definition
            name.toString val.type val.value none [] (mkMeta name.toString)]
        | _ => pure ()
      | .thmInfo val =>
        concepts := concepts ++ [ConceptData.theorem
          name.toString val.type val.value [] (mkMeta name.toString)]
      | _ => pure ()

  return concepts

/-- Create initial mathematical concepts -/
def seedConcepts : MetaM (List ConceptData) := do
  let mut concepts := []

  let mkMeta (name : String) (method : String := "seed") : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := method
  }

  -- Natural numbers
  let natType := mkConst ``Nat

  -- Zero
  let zero := mkConst ``Nat.zero
  concepts := concepts ++ [ConceptData.definition "zero" natType zero none [] (mkMeta "zero")]

  -- Successor
  let succType ← mkArrow natType natType
  let succ := mkConst ``Nat.succ
  concepts := concepts ++ [ConceptData.definition "succ" succType succ none [] (mkMeta "succ")]

  -- One
  let one := mkApp succ zero
  concepts := concepts ++ [ConceptData.definition "one" natType one none ["zero", "succ"] (mkMeta "one")]

  -- Two (to help pattern recognition)
  let two := mkApp succ one
  concepts := concepts ++ [ConceptData.definition "two" natType two none ["one", "succ"] (mkMeta "two")]

  -- Addition
  let addType ← mkArrow natType (← mkArrow natType natType)
  let add := mkConst ``Nat.add
  concepts := concepts ++ [ConceptData.definition "add" addType add none [] (mkMeta "add")]

  -- Basic theorem: 0 = 0
  let zeroEqZero := mkApp3 (mkConst ``Eq [levelOne]) natType zero zero
  let zeroEqZeroProof := mkApp2 (mkConst ``Eq.refl [levelOne]) natType zero
  concepts := concepts ++ [ConceptData.theorem "zero_eq_zero" zeroEqZero zeroEqZeroProof ["zero"] (mkMeta "zero_eq_zero")]

  -- to test lemma application heuristic
  let addComm := mkConst ``Nat.add_comm
  concepts := concepts ++ [ConceptData.theorem
  "add_comm"  -- name
  (← inferType addComm)
  addComm      -- proof-term
  []
  (mkMeta "add_comm")]

  return concepts

/-- Enhanced concept selection based on promise and diversity -/
def selectFocusConcepts (kb : KnowledgeBase) (maxConcepts : Nat) : List ConceptData :=
  -- Score concepts by multiple factors
  let scoredConcepts := kb.concepts.map fun c =>
    let meta := getConceptMetadata c
    let recencyBonus := if kb.recentConcepts.any (fun r => getConceptName r == getConceptName c) then 0.3 else 0.0
    let successBonus := meta.successCount.toFloat * 0.1
    let underexploredBonus := if meta.useCount < 3 then 0.2 else 0.0
    let depthPenalty := meta.specializationDepth.toFloat * 0.1
    let patternBonus := match c with
      | ConceptData.pattern _ _ instances _ => instances.length.toFloat * 0.05
      | _ => 0.0

    let score := meta.interestingness + recencyBonus + successBonus +
                 underexploredBonus + patternBonus - depthPenalty
    (c, score)

  -- Sort by score and take top concepts
  let sorted := scoredConcepts.toArray.qsort (·.2 > ·.2)

  -- Ensure diversity by limiting concepts of the same type
  Id.run do
    let mut selected : List ConceptData := []
    let mut typeCount : List (String × Nat) := []

    for (c, _) in sorted do
      let conceptType := match c with
        | ConceptData.definition _ _ _ _ _ m => m.generationMethod
        | ConceptData.theorem _ _ _ _ m => "theorem"
        | ConceptData.conjecture _ _ _ _ => "conjecture"
        | ConceptData.pattern _ _ _ _ => "pattern"
        | _ => "other"

      let currentCount := (typeCount.lookup conceptType).getD 0
      if currentCount < maxConcepts / 4 then  -- Limit each type
        selected := selected ++ [c]
        typeCount := typeCount.filter (·.1 != conceptType) ++ [(conceptType, currentCount + 1)]

      if selected.length >= maxConcepts then
        break

    selected

/-- Apply evolution heuristics to generate new concepts -/
def evolve (kb : KnowledgeBase) : MetaM (List Discovery) := do
  let heuristicRefs := kb.concepts.filterMap fun c => match c with
    | ConceptData.heuristicRef name _ meta => some (name, meta)
    | _ => none

  let mut discoveries := []

  -- Generate new numbers every other iteration
  if kb.iteration % 2 == 0 then
    if let some newNum ← generateNextNumber kb then
      discoveries := discoveries ++ [Discovery.mk [newNum] [] "Generated next number"]

  -- Use smart selection
  let focusedConcepts := selectFocusConcepts kb 50

  IO.println s!"[DEBUG] Focusing on {focusedConcepts.length} concepts (from {kb.recentConcepts.length} recent, {kb.concepts.length} total)"

  IO.println s!"[DEBUG] Invoking heuristics: {kb.heuristics.entries.map Prod.fst}"
  for (name, meta) in heuristicRefs do
    if let some heuristic := kb.heuristics.find? name then
      try
        let newConcepts ← heuristic kb.config focusedConcepts

        IO.println s!"[DEBUG] Heuristic {name} generated {newConcepts.length} concepts"

        -- Clean up new concepts against ALL existing concepts
        let cleanedConcepts ← cleanupConcepts kb.config kb.concepts newConcepts

        IO.println s!"[DEBUG] After cleanup: {cleanedConcepts.length} concepts"

        -- Verify all new concepts
        let mut verifiedConcepts := []
        for concept in cleanedConcepts do
          match concept with
          | ConceptData.definition _ t v _ _ _ =>
            if ← verifyDefinition t v then
              verifiedConcepts := verifiedConcepts ++ [concept]
          | ConceptData.theorem _ s p _ _ =>
            if ← verifyTheorem s p then
              verifiedConcepts := verifiedConcepts ++ [concept]
          | ConceptData.conjecture _ _ _ _ =>
            verifiedConcepts := verifiedConcepts ++ [concept]
          | ConceptData.pattern _ _ _ _ =>
            verifiedConcepts := verifiedConcepts ++ [concept]
          | _ => verifiedConcepts := verifiedConcepts ++ [concept]

        IO.println s!"[DEBUG] After verification: {verifiedConcepts.length} concepts"

        -- Limit number of concepts per heuristic
        let limitedConcepts := verifiedConcepts.take kb.config.maxConceptsPerIteration

        if limitedConcepts.length > 0 then
          discoveries := discoveries ++ [Discovery.mk limitedConcepts [] s!"Applied heuristic {meta.name}"]
      catch err =>
        let msg := err.toMessageData
        logInfo m!"[DEBUG] Error in heuristic {name}: {msg}"
        pure ()

  return discoveries

/-- Evaluate discoveries using task-based criteria -/
def evaluate (kb : KnowledgeBase) (discoveries : List Discovery) : MetaM (List ConceptData) := do
  let taskRefs := kb.concepts.filterMap fun c => match c with
    | ConceptData.taskRef name _ meta => some (name, meta)
    | _ => none

  let mut evaluatedConcepts := []

  for discovery in discoveries do
    for concept in discovery.newConcepts do
      let mut totalScore := 0.0
      let mut taskCount := 0

      for (name, _) in taskRefs do
        if let some eval := kb.evaluators.find? name then
          try
            let score ← eval (kb.concepts ++ [concept])
            totalScore := totalScore + score
            taskCount := taskCount + 1
          catch _ =>
            pure ()

      let avgScore := if taskCount > 0 then totalScore / taskCount.toFloat else 0.5
      let updatedConcept := updateConceptScore concept avgScore

      if avgScore > kb.config.pruneThreshold then
        evaluatedConcepts := evaluatedConcepts ++ [updatedConcept]

  return evaluatedConcepts

/-- Show discovered concepts more clearly -/
def showDiscoveredConcepts (concepts : List ConceptData) (showDetails : Bool := true) : MetaM Unit := do
  -- Group by type
  let conjectures := concepts.filter fun c => match c with
    | ConceptData.conjecture _ _ _ _ => true | _ => false
  let newTheorems := concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ m => m.generationMethod != "mined" | _ => false
  let patterns := concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true | _ => false
  let applications := concepts.filter fun c => match c with
    | ConceptData.definition _ _ _ _ _ m => m.generationMethod == "application" | _ => false
  let numbers := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => m.generationMethod == "number_generation" | _ => false
  let compositions := concepts.filter fun c => match c with
    | ConceptData.definition _ _ _ _ _ m => m.generationMethod == "composition" | _ => false

  if numbers.length > 0 then
    IO.println s!"\n🔢 New Numbers ({numbers.length}):"
    for n in numbers do
      IO.println s!"  - {getConceptName n}"

  if conjectures.length > 0 then
    IO.println s!"\n🔮 Conjectures ({conjectures.length}):"
    for c in conjectures.take 5 do
      match c with
      | ConceptData.conjecture name stmt evidence _ =>
        IO.println s!"  - {name}"
        IO.println s!"    Evidence: {evidence}"
      | _ => pure ()
    if conjectures.length > 5 then
      IO.println s!"  ... and {conjectures.length - 5} more"

  if newTheorems.length > 0 then
    IO.println s!"\n✓ Proven Theorems ({newTheorems.length}):"
    for t in newTheorems.take 5 do
      match t with
      | ConceptData.theorem name _ _ _ meta =>
        IO.println s!"  - {name}"
        IO.println s!"    Method: {meta.generationMethod}"
      | _ => pure ()

  if patterns.length > 0 then
    IO.println s!"\n🔍 Patterns ({patterns.length}):"
    for p in patterns do
      match p with
      | ConceptData.pattern name desc instances _ =>
        IO.println s!"  - {name}: {desc}"
        if showDetails && instances.length > 0 then
          IO.println s!"    Examples: {instances.take 3}"
      | _ => pure ()

  if applications.length > 0 then
    IO.println s!"\n🔧 Function Applications ({applications.length}):"
    for a in applications.take 3 do
      let name := getConceptName a
      IO.println s!"  - {name}"

  if compositions.length > 0 then
    IO.println s!"\n🔗 Function Compositions ({compositions.length}):"
    for c in compositions.take 3 do
      let name := getConceptName c
      IO.println s!"  - {name}"

/-- Update cache with new attempts -/
def updateCache (cache : ConceptCache) (newConcepts : List ConceptData) : ConceptCache :=
  let newApplications := newConcepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ m =>
      if m.generationMethod == "application" then
        let parts := n.splitOn "_applied_to_"
        if parts.length == 2 then some (parts[0]!, parts[1]!)
        else none
      else none
    | _ => none

  let newSpecializations := newConcepts.filterMap fun c => match c with
    | ConceptData.theorem n _ _ _ m =>
      if m.generationMethod == "specialization" then
        let parts := n.splitOn "_spec_"
        if parts.length == 2 then some (parts[0]!, parts[1]!)
        else none
      else none
    | _ => none

  { cache with
    attemptedApplications := cache.attemptedApplications ++ newApplications
    attemptedSpecializations := cache.attemptedSpecializations ++ newSpecializations
  }

/-- Main discovery loop -/
partial def discoveryLoop (kb : KnowledgeBase) (maxIterations : Nat) : MetaM KnowledgeBase := do
  if kb.iteration >= maxIterations then
    return kb

  IO.println s!"\n--- Iteration {kb.iteration + 1} ---"

  -- Show what we're focusing on
  if kb.recentConcepts.length > 0 then
    IO.println s!"Building on {kb.recentConcepts.length} recent discoveries:"
    for c in kb.recentConcepts.take 5 do
      IO.println s!"  - {getConceptName c}"

  let discoveries ← evolve kb
  let mut allNewConcepts := []
  for discovery in discoveries do
    allNewConcepts := allNewConcepts ++ discovery.newConcepts

  let evaluatedConcepts ← evaluate kb discoveries

  if evaluatedConcepts.length > 0 then
    showDiscoveredConcepts evaluatedConcepts

    -- Count by method manually
    IO.println s!"\n📊 Discovery Summary:"
    let methods := ["specialization", "application", "conjecture", "pattern_recognition",
                    "lemma_application", "number_generation", "composition", "pattern_extension"]
    for method in methods do
      let count := evaluatedConcepts.filter (fun c => (getConceptMetadata c).generationMethod == method) |>.length
      if count > 0 then
        IO.println s!"  {method}: {count} concepts"
  else
    IO.println "No new concepts discovered this iteration"

  -- Try to prove conjectures
  let mut provenConjectures := []
  let mut allConjectures := kb.concepts ++ evaluatedConcepts

  -- Remove conjectures that get proved
  let mut remainingConcepts := []

  for c in allConjectures do
    match c with
    | ConceptData.conjecture name stmt _ meta =>
      -- Check if we've failed this before
      let failedBefore := kb.failedProofs.any fun fa =>
        fa.statementStr == toString stmt && fa.attemptCount >= 3

      if !failedBefore then
        if let some proof ← tryProveConjecture stmt then
          IO.println s!"  ✓ Proved conjecture: {name}"
          let thm := ConceptData.theorem name stmt proof []
            { meta with generationMethod := "conjecture_proved" }
          provenConjectures := provenConjectures ++ [thm]

          -- Reward parent concepts for successful proof
          if let some parentName := meta.parent then
            remainingConcepts := remainingConcepts.map fun c' =>
              if getConceptName c' == parentName then
                updateConceptMetadata c' fun m =>
                  { m with successCount := m.successCount + 1 }
              else c'
        else
          -- Track failed attempt
          let stmtStr := toString stmt
          let mut newFailedProofs := kb.failedProofs
          match kb.failedProofs.find? (·.statementStr == stmtStr) with
          | some fa =>
            newFailedProofs := newFailedProofs.filter (·.statementStr != stmtStr) ++
              [{ fa with attemptCount := fa.attemptCount + 1, lastAttempt := kb.iteration }]
          | none =>
            newFailedProofs := newFailedProofs ++
              [{ statementStr := stmtStr, attemptCount := 1, lastAttempt := kb.iteration }]

          -- Keep unproven conjectures
          remainingConcepts := remainingConcepts ++ [c]
      else
        -- Skip conjectures we've failed too many times
        pure ()
    | _ =>
      remainingConcepts := remainingConcepts ++ [c]

  -- Update cache with new concepts
  let newCache := updateCache kb.cache evaluatedConcepts

  let newKb : KnowledgeBase := {
    concepts := remainingConcepts ++ provenConjectures
    recentConcepts := evaluatedConcepts ++ provenConjectures
    heuristics := kb.heuristics
    evaluators := kb.evaluators
    config := kb.config
    iteration := kb.iteration + 1
    history := kb.history ++ [(kb.iteration, (evaluatedConcepts ++ provenConjectures).map getConceptName)]
    cache := newCache
    failedProofs := kb.failedProofs
  }

  discoveryLoop newKb maxIterations

/--
Heuristic: apply any mined Eq-theorem whose left-hand side matches another concept's expression,
producing new theorems `thName_on_targetName` via lemma application.
-/
def lemmaApplicationHeuristic : HeuristicFn := fun config concepts => do
  let mut out : List ConceptData := []
  for c in concepts do
    match c with
    | ConceptData.theorem thName stmt proof deps meta => do
      let fn := stmt.getAppFn
      if fn.isConstOf ``Eq then
        let argsList := stmt.getAppArgs.toList
        match argsList with
        | α :: lhs :: rhs :: [] =>
          let lemmaName := Name.mkStr Name.anonymous thName
          for tgt in concepts do
            if let some tgtExpr := getConceptExpr tgt then
              if ← isDefEq lhs tgtExpr then
                -- Debug: matched lhs on target
                IO.println s!"[DEBUG][lemma_application] applying {thName} to {getConceptName tgt}"
                let eqConst := mkConst ``Eq [levelOne]
                let newStmt := mkApp3 eqConst α tgtExpr rhs
                let newProof := proof
                let newName := thName ++ "_on_" ++ getConceptName tgt
                let newMeta := { meta with
                  name := newName,
                  parent := some thName,
                  generationMethod := "lemma_application"
                }
                out := out ++ [ConceptData.theorem newName newStmt newProof deps newMeta]
        | _ => pure ()
    | _ => pure ()
  return out

/-- Use discovered patterns to guide new concept generation -/
def patternGuidedHeuristic : HeuristicFn := fun config concepts => do
  let patterns := concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true
    | _ => false

  let mut newConcepts := []

  for pattern in patterns do
    match pattern with
    | ConceptData.pattern "natural_number_sequence" _ instances _ =>
      -- If we have a sequence pattern, try to extend it
      let maxNum := instances.foldl (fun acc inst =>
        if inst.startsWith "num_" then
          max acc ((inst.drop 4).toNat?.getD 0)
        else if inst == "zero" then max acc 0
        else if inst == "one" then max acc 1
        else if inst == "two" then max acc 2
        else acc
      ) 0

      -- Generate the next few numbers in the sequence
      for i in [maxNum + 1:min (maxNum + 3) 10] do
        let numExpr := (List.range i).foldl (fun acc _ =>
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        let newConcept := ConceptData.definition s!"num_{i}"
          (mkConst ``Nat) numExpr none []
          { name := s!"num_{i}", created := 0, parent := some "natural_number_sequence",
            interestingness := 0.6, useCount := 0, successCount := 0,
            specializationDepth := 0, generationMethod := "pattern_extension" }
        newConcepts := newConcepts ++ [newConcept]

    | ConceptData.pattern name desc instances meta =>
      -- For function iteration patterns, try to continue the iteration
      if name.endsWith "_iteration_pattern" then
        -- Extract function name
        let funcName := name.dropRight "_iteration_pattern".length
        -- Find the function
        if let some funcConcept := concepts.find? fun c =>
          getConceptName c == funcName then
          match funcConcept with
          | ConceptData.definition _ _ funcVal _ _ _ =>
            -- Find highest iteration
            let maxIter := instances.foldl (fun acc inst =>
              if inst.startsWith s!"{funcName}_applied_to_" then
                let parts := inst.splitOn "_applied_to_"
                if parts.length >= 2 then
                  let lastPart := parts.getLast!
                  if lastPart.startsWith s!"{funcName}_applied_to_" then
                    acc + 1
                  else acc
                else acc
              else acc
            ) 0

            if maxIter < 5 then  -- Don't go too deep
              -- Find the last application and apply function again
              if let some lastApp := concepts.find? fun c =>
                instances.contains (getConceptName c) then
                if let some lastExpr := getConceptExpr lastApp then
                  let newApp := mkApp funcVal lastExpr
                  let newName := s!"{funcName}_iter_{maxIter + 1}"
                  let newType ← inferType newApp
                  newConcepts := newConcepts ++ [
                    ConceptData.definition newName newType newApp none [funcName]
                      { name := newName, created := 0, parent := some name,
                        interestingness := 0.5, useCount := 0, successCount := 0,
                        specializationDepth := maxIter + 1, generationMethod := "pattern_extension" }
                  ]
          | _ => pure ()
    | _ => pure ()

  return newConcepts

/-- Pattern recognition heuristic: identify mathematical patterns -/
def patternRecognitionHeuristic : HeuristicFn := fun config concepts => do
  if !config.enablePatternRecognition then
    return []

  let mut patterns := []

  -- Look for arithmetic sequences
  let numbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ m =>
      if n.startsWith "num_" || n == "zero" || n == "one" || n == "two" then
        some (n, v, m)
      else none
    | _ => none

  if numbers.length >= 3 then
    -- Check if we have 0, 1, 2...
    let mut hasSequence := false
    let mut sequenceNames := []

    for (n, _, _) in numbers do
      if n == "zero" || n == "one" || n == "two" || n.startsWith "num_" then
        sequenceNames := sequenceNames ++ [n]
        hasSequence := true

    if hasSequence && sequenceNames.length >= 3 then
      let patternMeta := {
        name := "natural_number_sequence"
        created := 0
        parent := none
        interestingness := 0.8
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "pattern_recognition"
      }
      patterns := patterns ++ [
        ConceptData.pattern
          "natural_number_sequence"
          "Sequence: 0, 1, 2, ... (natural numbers via successor)"
          sequenceNames
          patternMeta
      ]

  -- Look for function iteration patterns
  let applications := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m =>
      m.generationMethod == "application" && ((n.splitOn "_applied_to_").length > 1)
    | _ => false

  if applications.length >= 3 then
    -- Check for repeated application of same function
    let mut functionApplications : List (String × List String) := []

    for c in applications do
      let name := getConceptName c
      let parts := name.splitOn "_applied_to_"
      if parts.length > 0 then
        let func := parts.head!
        match functionApplications.find? (·.1 == func) with
        | some (_, apps) =>
          functionApplications := functionApplications.filter (·.1 != func) ++ [(func, apps ++ [name])]
        | none =>
          functionApplications := functionApplications ++ [(func, [name])]

    for (func, apps) in functionApplications do
      if apps.length >= 2 then
        let patternMeta := {
          name := s!"{func}_iteration_pattern"
          created := 0
          parent := none
          interestingness := 0.7
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "pattern_recognition"
        }
        patterns := patterns ++ [
          ConceptData.pattern
            s!"{func}_iteration_pattern"
            s!"Repeated application of {func}"
            apps
            patternMeta
        ]

  return patterns

/-- Conjecture generation heuristic with evidence calculation -/
def conjectureGenerationHeuristic : HeuristicFn := fun config concepts => do
  if !config.enableConjectures then
    return []

  let mut conjectures := []
  let kb : KnowledgeBase := {
    concepts := concepts
    recentConcepts := []
    heuristics := HeuristicRegistry.empty
    evaluators := EvaluationRegistry.empty
    config := config
    iteration := 0
    history := []
    cache := {}
    failedProofs := []
  }

  -- Find interesting theorems to generalize/combine
  let theorems := concepts.filterMap fun c => match c with
    | ConceptData.theorem n s p d m =>
      if !((n.splitOn "_spec_").length > 1) then some (n, s, p, d, m)
      else none
    | _ => none

  -- PATTERN 1: Look for function composition patterns
  let functions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if t.isForall && !((n.splitOn "_applied_").length > 1) then some (n, v, t)
      else none
    | _ => none

  -- For each pair of functions, try to create composition conjectures
  for (f1_name, f1_val, f1_type) in functions do
    for (f2_name, f2_val, f2_type) in functions do
      if f1_name != f2_name && f1_name.length < 10 && f2_name.length < 10 then
        -- Check if we can compose them by looking at types
        match f1_type with
        | .forallE _ argType1 _ _ =>
          match f2_type with
          | .forallE _ argType2 resultType2 _ =>
            -- If f2's result type matches f1's argument type, we can compose
            if ← isDefEq resultType2 argType1 then
              -- Create a conjecture about the composition
              let natType := mkConst ``Nat
              let zero := mkConst ``Nat.zero
              let one := mkApp (mkConst ``Nat.succ) zero

              -- f1(f2(0)) = ?
              let comp_zero := mkApp f1_val (mkApp f2_val zero)
              -- Maybe it equals f1(0) or f2(0) or 0?
              let candidates : List Expr := [mkApp f1_val zero, mkApp f2_val zero, zero, one]

              let mut idx := 0
              for candidate in candidates do
                let stmt := mkApp3 (mkConst ``Eq [levelOne]) natType comp_zero candidate
                let evidence ← calculateConjectureEvidence stmt kb

                conjectures := conjectures ++ [
                  ConceptData.conjecture
                    s!"{f1_name}_comp_{f2_name}_eq_{idx}"
                    stmt
                    evidence
                    { name := s!"{f1_name}_comp_{f2_name}_eq_{idx}",
                      created := 0, parent := none, interestingness := 0.7,
                      useCount := 0, successCount := 0, specializationDepth := 1,
                      generationMethod := "composition_pattern" }
                ]
                idx := idx + 1
          | _ => pure ()
        | _ => pure ()
  /-
  -- TODO: commented out because causing errors
  -- PATTERN 2: Look for preservation properties
  for (thm_name, stmt, _, _, _) in theorems do
    -- Look for theorems that might be properties
    if (thm_name.splitOn "eq").length > 1 || (thm_name.splitOn "comm").length > 1 || (thm_name.splitOn "assoc").length > 1 then
      for (fn_name, fn_val, fn_type) in functions do
        if fn_name != "zero" && fn_name != "one" && fn_name != "two" then
          let natType := mkConst ``Nat
          let x := mkConst ``Nat.zero
          let y := mkApp (mkConst ``Nat.succ) x

          -- Create a simple preservation conjecture
          let fx := mkApp fn_val x
          let fy := mkApp fn_val y
          let preservationStmt := mkApp3 (mkConst ``Eq [levelOne]) natType fx fy
          let evidence ← calculateConjectureEvidence preservationStmt kb

          conjectures := conjectures ++ [
            ConceptData.conjecture
              s!"{fn_name}_preserves_{thm_name}_maybe"
              preservationStmt
              evidence
              { name := s!"{fn_name}_preserves_{thm_name}_maybe",
                created := 0, parent := some thm_name, interestingness := 0.5,
                useCount := 0, successCount := 0, specializationDepth := 1,
                generationMethod := "preservation_pattern" }
          ]

  -- PATTERN 3: Identity and fixed point conjectures
  for (fn_name, fn_val, _) in functions do
    if fn_name != "succ" then
      let natType := mkConst ``Nat
      let zero := mkConst ``Nat.zero

      -- Conjecture: f(0) = 0 (zero is a fixed point)
      let f_zero := mkApp fn_val zero
      let fixedPointStmt := mkApp3 (mkConst ``Eq [levelOne]) natType f_zero zero
      let evidence ← calculateConjectureEvidence fixedPointStmt kb

      conjectures := conjectures ++ [
        ConceptData.conjecture
          s!"{fn_name}_fixed_point_zero"
          fixedPointStmt
          evidence
          { name := s!"{fn_name}_fixed_point_zero",
            created := 0, parent := none, interestingness := 0.6,
            useCount := 0, successCount := 0, specializationDepth := 1,
            generationMethod := "fixed_point_search" }
      ]

  -- Add homomorphism pattern
  -- Pattern: f(x + y) = f(x) + f(y)
  for (fn_name, fn_val, fn_type) in functions do
    match fn_type with
    | .forallE _ (.const ``Nat _) (.const ``Nat _) _ =>
      let natType := mkConst ``Nat
      let x := mkBVar 1
      let y := mkBVar 0
      let add := mkConst ``Nat.add
      let xy := mkApp2 add x y
      let fxy := mkApp fn_val xy
      let fx := mkApp fn_val x
      let fy := mkApp fn_val y
      let fx_plus_fy := mkApp2 add fx fy

      let homoStmt := mkForall `x .default natType $
        mkForall `y .default natType $
          mkApp3 (mkConst ``Eq [levelOne]) natType fxy fx_plus_fy

      let evidence ← calculateConjectureEvidence homoStmt kb

      conjectures := conjectures ++ [
        ConceptData.conjecture
          s!"{fn_name}_homomorphism"
          homoStmt
          evidence
          { name := s!"{fn_name}_homomorphism",
            created := 0, parent := some fn_name, interestingness := 0.7,
            useCount := 0, successCount := 0, specializationDepth := 1,
            generationMethod := "homomorphism_pattern" }
      ]
    | _ => pure ()
  -/
  -- Still keep some original commutativity conjectures
  let numbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ m =>
      if n == "zero" || n == "one" || n == "two" || n.startsWith "num_" then
        some (n, v, m)
      else none
    | _ => none

  if numbers.length >= 2 then
    match numbers with
    | (n1, v1, _) :: (n2, v2, _) :: _ =>
      if let some (ConceptData.definition _ _ addFn _ _ _) :=
        concepts.find? fun c => match c with
          | ConceptData.definition n _ _ _ _ _ => n == "add"
          | _ => false then

        let natType := mkConst ``Nat
        let lhs := mkApp2 addFn v1 v2
        let rhs := mkApp2 addFn v2 v1
        let stmt := mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
        let evidence ← calculateConjectureEvidence stmt kb

        conjectures := conjectures ++ [
          ConceptData.conjecture
            s!"add_comm_{n1}_{n2}"
            stmt
            evidence
            { name := s!"add_comm_{n1}_{n2}",
              created := 0, parent := none, interestingness := 0.3,
              useCount := 0, successCount := 0, specializationDepth := 1,
              generationMethod := "commutativity" }
        ]
    | _ => pure ()

  IO.println s!"[DEBUG] Total conjectures generated: {conjectures.length}"
  return conjectures

/-- Specialization heuristic: create specific instances -/
def specializationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  -- Find universal theorems
  for c in concepts do
    match c with
    | ConceptData.theorem name stmt proof deps meta =>
      -- Skip if already deeply specialized
      if meta.specializationDepth >= config.maxSpecializationDepth then
        continue

      -- Skip theorems that are already specializations
      if (name.splitOn "_spec_").length > 1 then
        continue

      -- Check if it's a forall statement
      match ← whnf stmt with
      | .forallE _ varType body _ =>
        -- Try to specialize with known terms of the right type
        let mut specializationCount := 0
        for c2 in concepts do
          if specializationCount >= 5 then  -- Limit specializations per theorem
            break

          match c2 with
          | ConceptData.definition defName _ defValue _ _ defMeta =>
            -- Skip complex definitions for specialization
            if defMeta.specializationDepth > 1 then
              continue

            let defType ← inferType defValue
            if ← isDefEq defType varType then
              -- Create specialized theorem
              let specStmt := body.instantiate1 defValue
              let specProof := mkApp proof defValue
              let specName := s!"{name}_spec_{defName}"
              let newMeta := { meta with
                name := specName
                parent := some name
                interestingness := 0.0
                specializationDepth := meta.specializationDepth + 1
                generationMethod := "specialization"
              }
              newConcepts := newConcepts ++ [
                ConceptData.theorem specName specStmt specProof (deps ++ [defName]) newMeta
              ]
              specializationCount := specializationCount + 1
          | _ => pure ()
      | _ => pure ()
    | _ => pure ()

  return newConcepts

/-- Function application heuristic with caching -/
def applicationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  -- Get cache from somewhere (we'd need to pass kb to heuristics for this to work properly)
  -- For now, we'll just check if the concept already exists

  let definitions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m => some (n, t, v, d, m)
    | _ => none

  for (fname, ftype, fvalue, fdeps, fmeta) in definitions do
    -- Skip deeply nested applications
    if fmeta.specializationDepth >= config.maxSpecializationDepth then
      continue

    -- Check if it's a function type
    match ← whnf ftype with
    | .forallE _ argType _ _ =>
      -- Find suitable arguments
      let mut applicationCount := 0
      for (aname, _, avalue, adeps, ameta) in definitions do
        if applicationCount >= 3 then  -- Limit applications per function
          break

        -- Check if this combination already exists
        let proposedName := s!"{fname}_applied_to_{aname}"
        let alreadyTried := concepts.any (fun c => getConceptName c == proposedName)

        if !alreadyTried && fname != aname && ameta.specializationDepth < 2 then
          let atype ← inferType avalue
          if ← isDefEq atype argType then
            -- Apply function to argument
            let resultValue := mkApp fvalue avalue
            let resultType ← inferType resultValue

            -- Check if this reduces to something simpler
            let _ ← whnf resultValue
            let resultName := proposedName

            let newMeta := {
              name := resultName
              created := 0
              parent := some fname
              interestingness := 0.0
              useCount := 0
              successCount := 0
              specializationDepth := max fmeta.specializationDepth ameta.specializationDepth + 1
              generationMethod := "application"
            }
            newConcepts := newConcepts ++ [
              ConceptData.definition resultName resultType resultValue none (fdeps ++ adeps ++ [aname]) newMeta
            ]
            applicationCount := applicationCount + 1
    | _ => pure ()

  return newConcepts

/-- Compose existing concepts to create new ones -/
def compositionHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  -- Find composable functions
  let functions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if t.isForall && m.useCount > 0 && m.specializationDepth < 2 then
        some (n, t, v, d, m)
      else none
    | _ => none

  -- Try function composition where types align
  for (f1, t1, v1, d1, m1) in functions do
    for (f2, t2, v2, d2, m2) in functions do
      if f1 != f2 then
        -- Check if we can compose f1 ∘ f2
        match (t1, t2) with
        | (.forallE _ a1 b1 _, .forallE _ a2 b2 _) =>
          if ← isDefEq b2 a1 then  -- f2's output matches f1's input
            -- Check if this composition already exists
            let compName := s!"{f1}_compose_{f2}"
            let alreadyExists := concepts.any (fun c => getConceptName c == compName)

            if !alreadyExists then
              -- Create composition
              let compType ← mkArrow a2 b1
              let compValue := mkLambda `x .default a2 $
                mkApp v1 (mkApp v2 (mkBVar 0))

              newConcepts := newConcepts ++ [
                ConceptData.definition compName compType compValue none (d1 ++ d2)
                  { name := compName, created := 0, parent := some f1,
                    interestingness := 0.7, useCount := 0, successCount := 0,
                    specializationDepth := max m1.specializationDepth m2.specializationDepth + 1,
                    generationMethod := "composition" }
              ]
        | _ => pure ()

  return newConcepts

/-- Complexity evaluation task -/
def complexityTask : EvaluationFn := fun concepts => do
  if let some concept := concepts.getLast? then
    match concept with
    | ConceptData.definition _ t v _ _ meta =>
      -- Measure expression complexity
      let typeSize := (exprSize t).toFloat
      let valueSize := (exprSize v).toFloat
      let depthPenalty := meta.specializationDepth.toFloat * 0.1
      let complexity := typeSize + valueSize + depthPenalty * 10.0
      -- Prefer simpler concepts
      return 1.0 / (1.0 + complexity / 10.0)
    | ConceptData.theorem _ s p _ meta =>
      let stmtSize := (exprSize s).toFloat
      let proofSize := (exprSize p).toFloat
      let depthPenalty := meta.specializationDepth.toFloat * 0.1
      let complexity := stmtSize + proofSize / 2.0 + depthPenalty * 10.0
      return 1.0 / (1.0 + complexity / 20.0)
    | ConceptData.conjecture _ _ evidence _ =>
      -- Conjectures are interesting based on evidence
      return evidence
    | ConceptData.pattern _ _ instances _ =>
      -- Patterns are interesting based on number of instances
      return min 1.0 (instances.length.toFloat / 5.0)
    | _ => return 0.5
  else
    return 0.5

/-- Novelty evaluation task -/
def noveltyTask : EvaluationFn := fun concepts => do
  if let some newConcept := concepts.getLast? then
    let name := getConceptName newConcept
    let meta := getConceptMetadata newConcept

    -- Bonus for conjectures and patterns
    let typeBonus := match newConcept with
      | ConceptData.conjecture _ _ _ _ => 0.2
      | ConceptData.pattern _ _ _ _ => 0.3
      | _ => 0.0

    -- Penalize deep specializations
    let depthPenalty := meta.specializationDepth.toFloat * 0.2

    -- Check how different the name is from existing concepts
    let mut maxSimilarity := 0.0
    for c in concepts.dropLast do
      let existingName := getConceptName c
      -- Simple similarity: count common characters
      let commonChars := name.toList.filter (existingName.toList.contains ·) |>.length
      let similarity := commonChars.toFloat / (max name.length existingName.length).toFloat
      maxSimilarity := max maxSimilarity similarity

    -- Return novelty score
    return max 0.1 (1.0 - maxSimilarity * 0.5 - depthPenalty + typeBonus)
  else
    return 0.5

/-- Pattern importance evaluation task -/
def patternImportanceTask : EvaluationFn := fun concepts => do
  if let some concept := concepts.getLast? then
    match concept with
    | ConceptData.pattern _ _ instances _ =>
      -- Patterns with more instances are more important
      let instanceBonus := instances.length.toFloat / 10.0
      -- Patterns that connect different concept types are valuable
      let mut diversityScore := 0.0
      let mut hasNumbers := false
      let mut hasApplications := false
      for inst in instances do
        if inst.startsWith "num_" || inst == "zero" || inst == "one" then
          hasNumbers := true
        if (inst.splitOn "_applied_to_").length > 1 then
          hasApplications := true
      if hasNumbers && hasApplications then
        diversityScore := 0.3

      return min 1.0 (0.5 + instanceBonus + diversityScore)
    | _ =>
      -- Use default complexity evaluation for non-patterns
      complexityTask concepts
  else
    return 0.5

/-- Initialize system with seed concepts and heuristics -/
def initializeSystem (config : DiscoveryConfig) (useMining : Bool := true) : MetaM KnowledgeBase := do
  let basicMeta : ConceptMetadata := {
    name := "initial"
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "initial"
  }

  -- Get seed concepts
  let mut initialConcepts ← seedConcepts

  -- Optionally add some mined concepts
  if useMining then
    let minedConcepts ← mineEnvironment ["Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul"] ["Mathlib.Algebra.Group", "Mathlib.Algebra.Ring"]
    -- Clean up mined concepts against existing
    let cleanedMined ← cleanupConcepts config initialConcepts minedConcepts
    initialConcepts := initialConcepts ++ cleanedMined.take 300

  -- Create heuristic references
  let specHeuristicRef := ConceptData.heuristicRef
    "specialization"
    "Create specific instances of universal theorems"
    { basicMeta with name := "specialization" }

  let appHeuristicRef := ConceptData.heuristicRef
    "application"
    "Apply functions to suitable arguments"
    { basicMeta with name := "application" }

  let lemmaAppHeuristicRef := ConceptData.heuristicRef
    "lemma_application"
    "Apply any mined Eq-theorem whose LHS matches another concept"
    { basicMeta with name := "lemma_application" }

  let patternHeuristicRef := ConceptData.heuristicRef
    "pattern_recognition"
    "Identify mathematical patterns in discovered concepts"
    { basicMeta with name := "pattern_recognition" }

  let conjectureHeuristicRef := ConceptData.heuristicRef
    "conjecture_generation"
    "Generate plausible mathematical conjectures"
    { basicMeta with name := "conjecture_generation" }

  let compositionHeuristicRef := ConceptData.heuristicRef
    "composition"
    "Compose functions to create new concepts"
    { basicMeta with name := "composition" }

  let patternGuidedHeuristicRef := ConceptData.heuristicRef
    "pattern_guided"
    "Use discovered patterns to guide generation"
    { basicMeta with name := "pattern_guided" }

  -- Create task references
  let complexityTaskRef := ConceptData.taskRef
    "complexity"
    "Prefer simpler concepts"
    { basicMeta with name := "complexity" }

  let noveltyTaskRef := ConceptData.taskRef
    "novelty"
    "Prefer novel concepts"
    { basicMeta with name := "novelty" }

  let patternTaskRef := ConceptData.taskRef
    "pattern_importance"
    "Evaluate importance of discovered patterns"
    { basicMeta with name := "pattern_importance" }

  -- Build registries
  let mut heuristics : HeuristicRegistry := HeuristicRegistry.empty
  heuristics := heuristics.insert "specialization" specializationHeuristic
  heuristics := heuristics.insert "application" applicationHeuristic
  heuristics := heuristics.insert "lemma_application" lemmaApplicationHeuristic
  heuristics := heuristics.insert "pattern_recognition" patternRecognitionHeuristic
  heuristics := heuristics.insert "conjecture_generation" conjectureGenerationHeuristic
  heuristics := heuristics.insert "composition" compositionHeuristic
  heuristics := heuristics.insert "pattern_guided" patternGuidedHeuristic

  let mut evaluators : EvaluationRegistry := EvaluationRegistry.empty
  evaluators := evaluators.insert "complexity" complexityTask
  evaluators := evaluators.insert "novelty" noveltyTask
  evaluators := evaluators.insert "pattern_importance" patternImportanceTask

  let allConcepts := initialConcepts ++ [
      specHeuristicRef, appHeuristicRef, lemmaAppHeuristicRef,
      patternHeuristicRef, conjectureHeuristicRef, compositionHeuristicRef,
      patternGuidedHeuristicRef, complexityTaskRef, noveltyTaskRef, patternTaskRef
    ]
  return {
    concepts := allConcepts
    recentConcepts := allConcepts
    heuristics := heuristics
    evaluators := evaluators
    config := config
    iteration := 0
    history := []
    cache := {}
    failedProofs := []
  }

/-- Get concept interestingness -/
def getInterestingness (c : ConceptData) : Float :=
  (getConceptMetadata c).interestingness

/-- Show concept statistics -/
def showConceptStats (concepts : List ConceptData) : IO Unit := do
  let defs := concepts.filter fun c => match c with
    | ConceptData.definition _ _ _ _ _ _ => true
    | _ => false
  let thms := concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ _ => true
    | _ => false
  let conjs := concepts.filter fun c => match c with
    | ConceptData.conjecture _ _ _ _ => true
    | _ => false
  let patterns := concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true
    | _ => false

  -- Build depth histogram manually
  let mut depthCounts : List (Nat × Nat) := []
  for c in concepts do
    let depth := (getConceptMetadata c).specializationDepth
    match depthCounts.find? (·.1 == depth) with
    | some (_, count) =>
      depthCounts := depthCounts.filter (·.1 != depth) ++ [(depth, count + 1)]
    | none =>
      depthCounts := depthCounts ++ [(depth, 1)]

  IO.println s!"\nDefinitions: {defs.length}"
  IO.println s!"Theorems: {thms.length}"
  IO.println s!"Conjectures: {conjs.length}"
  IO.println s!"Patterns: {patterns.length}"
  IO.println s!"\nDepth distribution:"
  let sorted := depthCounts.toArray.qsort (·.1 < ·.1)
  for (depth, count) in sorted do
    IO.println s!"  Depth {depth}: {count} concepts"

/-- Run the discovery system -/
def runDiscovery (maxIterations : Nat := 10) (useMining : Bool := false) (config : DiscoveryConfig := {}) : MetaM Unit := do
  IO.println "=== Starting Eurisko Discovery System ==="
  IO.println s!"Config: maxDepth={config.maxSpecializationDepth}, maxPerIter={config.maxConceptsPerIteration}"
  IO.println s!"Features: conjectures={config.enableConjectures}, patterns={config.enablePatternRecognition}"
  IO.println s!"Mining mode: {if useMining then "ON" else "OFF"}"
  IO.println "Initializing with mathematical seed concepts..."

  let kb ← initializeSystem config useMining

  IO.println s!"\nInitial concepts ({kb.concepts.length}):"
  showConceptStats kb.concepts

  let finalKb ← discoveryLoop kb maxIterations

  IO.println s!"\n=== Discovery Complete ==="
  IO.println s!"Total concepts: {finalKb.concepts.length}"
  showConceptStats finalKb.concepts

  -- Show discovered patterns
  let patterns := finalKb.concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true
    | _ => false

  if patterns.length > 0 then
    IO.println s!"\nDiscovered Patterns:"
    for p in patterns do
      match p with
      | ConceptData.pattern name desc instances _ =>
        IO.println s!"  - {name}: {desc}"
        IO.println s!"    Instances: {instances}"
      | _ => pure ()

  -- Show top concepts
  let sorted := finalKb.concepts.toArray.qsort fun c1 c2 =>
    getInterestingness c1 > getInterestingness c2

  IO.println s!"\nTop discovered concepts:"
  for i in [:min 20 sorted.size] do
    if h : i < sorted.size then
      let c := sorted[i]
      let meta := getConceptMetadata c
      match c with
      | ConceptData.conjecture name _ evidence _ =>
        IO.println s!"  {name} (CONJECTURE, evidence: {evidence}, score: {(getInterestingness c).toString})"
      | ConceptData.pattern name _ _ _ =>
        IO.println s!"  {name} (PATTERN, score: {(getInterestingness c).toString})"
      | _ =>
        IO.println s!"  {getConceptName c} (score: {(getInterestingness c).toString}, depth: {meta.specializationDepth})"

end LeanDisco
