import Lean
import Lean.Meta.Basic
import Lean.Elab.Command

open Lean Meta Elab

/-
# Eurisko-Inspired Discovery System for Lean

This system represents mathematical concepts, heuristics, and discovery tasks
as first-class objects in Lean, enabling automated mathematical discovery
with formal verification.
-/

namespace Eurisko

/-- Configuration for controlling discovery -/
structure DiscoveryConfig where
  maxSpecializationDepth : Nat := 2
  maxConceptsPerIteration : Nat := 50
  pruneThreshold : Float := 0.3
  deduplicateConcepts : Bool := true
  canonicalizeConcepts : Bool := true
  filterInternalProofs : Bool := true

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
    (canonicalValue : Option Expr) →  -- Cached canonical form
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

/-- Result of applying a heuristic or evolution step -/
structure Discovery where
  newConcepts : List ConceptData
  modifiedConcepts : List ConceptData
  explanation : String

/-- Knowledge base containing all discovered concepts -/
structure KnowledgeBase where
  concepts : List ConceptData
  heuristics : HeuristicRegistry
  evaluators : EvaluationRegistry
  config : DiscoveryConfig
  iteration : Nat
  history : List (Nat × List String)

/-- Extract concept name -/
def getConceptName : ConceptData → String
  | ConceptData.definition n _ _ _ _ _ => n
  | ConceptData.theorem n _ _ _ _ => n
  | ConceptData.conjecture n _ _ _ => n
  | ConceptData.heuristicRef n _ _ => n
  | ConceptData.taskRef n _ _ => n

/-- Get concept metadata -/
def getConceptMetadata : ConceptData → ConceptMetadata
  | ConceptData.definition _ _ _ _ _ m => m
  | ConceptData.theorem _ _ _ _ m => m
  | ConceptData.conjecture _ _ _ m => m
  | ConceptData.heuristicRef _ _ m => m
  | ConceptData.taskRef _ _ m => m

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

/-- Canonicalize a concept to its simplest form -/
def canonicalizeConcept (c : ConceptData) : MetaM ConceptData := do
  match c with
  | ConceptData.definition n t v cached deps meta =>
    if cached.isSome then
      return c  -- Already canonicalized
    else
      let v' ← whnf v
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

/-- Deduplicate concepts by canonical form, checking against existing concepts -/
def deduplicateAgainstExisting (existing : List ConceptData) (newConcepts : List ConceptData) : MetaM (List ConceptData) := do
  let mut result : List ConceptData := []

  -- First collect all existing expressions
  let mut existingExprs : List (Expr × String) := []
  for c in existing do
    if let some expr := getConceptExpr c then
      let expr' ← whnf expr
      existingExprs := (expr', getConceptName c) :: existingExprs

  -- Check each new concept
  for c in newConcepts do
    if let some expr := getConceptExpr c then
      let expr' ← whnf expr
      let mut isDuplicate := false

      -- Check against existing concepts
      for (existingExpr, _) in existingExprs do
        if ← exprsEqual expr' existingExpr then
          isDuplicate := true
          break

      -- Also check against already processed new concepts
      for processed in result do
        if let some processedExpr := getConceptExpr processed then
          let processedExpr' ← whnf processedExpr
          if ← exprsEqual expr' processedExpr' then
            isDuplicate := true
            break

      if !isDuplicate then
        result := c :: result
    else
      -- Keep non-expression concepts (heuristics, tasks)
      result := c :: result

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

  return cleaned

/-- Update concept's interestingness score -/
def updateConceptScore (c : ConceptData) (score : Float) : ConceptData :=
  match c with
  | ConceptData.definition n t v cached d m =>
      ConceptData.definition n t v cached d { m with interestingness := score }
  | ConceptData.theorem n s p d m =>
      ConceptData.theorem n s p d { m with interestingness := score }
  | ConceptData.conjecture n s e m =>
      ConceptData.conjecture n s e { m with interestingness := score }
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

/-- Check if a constant should be included based on filters -/
def shouldIncludeConstant (name : Name) (allowedPrefixes : List String) : Bool :=
  allowedPrefixes.any (·.isPrefixOf name.toString)

/-- Mine concepts from the Lean environment -/
def mineEnvironment (allowedPrefixes : List String := ["Nat", "Int", "List"]) : MetaM (List ConceptData) := do
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
    if shouldIncludeConstant name allowedPrefixes && !isInternalProofTerm name.toString then
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

  -- Addition
  let addType ← mkArrow natType (← mkArrow natType natType)
  let add := mkConst ``Nat.add
  concepts := concepts ++ [ConceptData.definition "add" addType add none [] (mkMeta "add")]

  return concepts

/-- Apply evolution heuristics to generate new concepts -/
def evolve (kb : KnowledgeBase) : MetaM (List Discovery) := do
  let heuristicRefs := kb.concepts.filterMap fun c => match c with
    | ConceptData.heuristicRef name _ meta => some (name, meta)
    | _ => none

  let mut discoveries := []

  for (name, meta) in heuristicRefs do
    if let some heuristic := kb.heuristics.find? name then
      try
        let newConcepts ← heuristic kb.config kb.concepts

        -- Clean up new concepts against ALL existing concepts
        let cleanedConcepts ← cleanupConcepts kb.config kb.concepts newConcepts

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
          | _ => verifiedConcepts := verifiedConcepts ++ [concept]

        -- Limit number of concepts per heuristic
        let limitedConcepts := verifiedConcepts.take kb.config.maxConceptsPerIteration

        if limitedConcepts.length > 0 then
          discoveries := discoveries ++ [Discovery.mk limitedConcepts [] s!"Applied heuristic {meta.name}"]
      catch _ =>
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

/-- Main discovery loop -/
partial def discoveryLoop (kb : KnowledgeBase) (maxIterations : Nat) : MetaM KnowledgeBase := do
  if kb.iteration >= maxIterations then
    return kb

  IO.println s!"\n--- Iteration {kb.iteration + 1} ---"

  let discoveries ← evolve kb
  let mut allNewConcepts := []
  for discovery in discoveries do
    allNewConcepts := allNewConcepts ++ discovery.newConcepts

  let evaluatedConcepts ← evaluate kb discoveries

  if evaluatedConcepts.length > 0 then
    IO.println s!"Discovered {evaluatedConcepts.length} new concepts:"
    for c in evaluatedConcepts.take 10 do  -- Show first 10
      IO.println s!"  - {getConceptName c} (depth: {(getConceptMetadata c).specializationDepth})"
  else
    IO.println "No new concepts discovered this iteration"

  let newKb : KnowledgeBase := {
    concepts := kb.concepts ++ evaluatedConcepts
    heuristics := kb.heuristics
    evaluators := kb.evaluators
    config := kb.config
    iteration := kb.iteration + 1
    history := kb.history ++ [(kb.iteration, evaluatedConcepts.map getConceptName)]
  }

  discoveryLoop newKb maxIterations

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

/-- Function application heuristic: apply functions to suitable arguments -/
def applicationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

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

        if fname != aname && ameta.specializationDepth < 2 then
          let atype ← inferType avalue
          if ← isDefEq atype argType then
            -- Apply function to argument
            let resultValue := mkApp fvalue avalue
            let resultType ← inferType resultValue

            -- Check if this reduces to something simpler
            let _ ← whnf resultValue
            let resultName := s!"{fname}_applied_to_{aname}"

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

/-- Expression size helper -/
def exprSize : Expr → Nat
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
    | _ => return 0.5
  else
    return 0.5

/-- Novelty evaluation task -/
def noveltyTask : EvaluationFn := fun concepts => do
  if let some newConcept := concepts.getLast? then
    let name := getConceptName newConcept
    let meta := getConceptMetadata newConcept

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

    -- Return novelty score (inverse of similarity minus depth penalty)
    return max 0.1 (1.0 - maxSimilarity * 0.5 - depthPenalty)
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
    let minedConcepts ← mineEnvironment ["Nat.zero", "Nat.succ", "Nat.add"]
    -- Clean up mined concepts against existing
    let cleanedMined ← cleanupConcepts config initialConcepts minedConcepts
    initialConcepts := initialConcepts ++ cleanedMined.take 10

  -- Create heuristic references
  let specHeuristicRef := ConceptData.heuristicRef
    "specialization"
    "Create specific instances of universal theorems"
    { basicMeta with name := "specialization" }

  let appHeuristicRef := ConceptData.heuristicRef
    "application"
    "Apply functions to suitable arguments"
    { basicMeta with name := "application" }

  -- Create task references
  let complexityTaskRef := ConceptData.taskRef
    "complexity"
    "Prefer simpler concepts"
    { basicMeta with name := "complexity" }

  let noveltyTaskRef := ConceptData.taskRef
    "novelty"
    "Prefer novel concepts"
    { basicMeta with name := "novelty" }

  -- Build registries
  let mut heuristics : HeuristicRegistry := HeuristicRegistry.empty
  heuristics := heuristics.insert "specialization" specializationHeuristic
  heuristics := heuristics.insert "application" applicationHeuristic

  let mut evaluators : EvaluationRegistry := EvaluationRegistry.empty
  evaluators := evaluators.insert "complexity" complexityTask
  evaluators := evaluators.insert "novelty" noveltyTask

  return {
    concepts := initialConcepts ++ [specHeuristicRef, appHeuristicRef, complexityTaskRef, noveltyTaskRef]
    heuristics := heuristics
    evaluators := evaluators
    config := config
    iteration := 0
    history := []
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
  IO.println s!"\nDepth distribution:"
  let sorted := depthCounts.toArray.qsort (·.1 < ·.1)
  for (depth, count) in sorted do
    IO.println s!"  Depth {depth}: {count} concepts"

/-- Run the discovery system -/
def runDiscovery (maxIterations : Nat := 10) (useMining : Bool := true) (config : DiscoveryConfig := {}) : MetaM Unit := do
  IO.println "=== Starting Eurisko Discovery System ==="
  IO.println s!"Config: maxDepth={config.maxSpecializationDepth}, maxPerIter={config.maxConceptsPerIteration}"
  IO.println s!"Mining mode: {if useMining then "ON" else "OFF"}"
  IO.println "Initializing with mathematical seed concepts..."

  let kb ← initializeSystem config useMining

  IO.println s!"\nInitial concepts ({kb.concepts.length}):"
  showConceptStats kb.concepts

  let finalKb ← discoveryLoop kb maxIterations

  IO.println s!"\n=== Discovery Complete ==="
  IO.println s!"Total concepts: {finalKb.concepts.length}"
  showConceptStats finalKb.concepts

  -- Show top concepts
  let sorted := finalKb.concepts.toArray.qsort fun c1 c2 =>
    getInterestingness c1 > getInterestingness c2

  IO.println s!"\nTop discovered concepts:"
  for i in [:min 15 sorted.size] do
    if h : i < sorted.size then
      let c := sorted[i]
      let meta := getConceptMetadata c
      IO.println s!"  {getConceptName c} (score: {(getInterestingness c).toString}, depth: {meta.specializationDepth}, method: {meta.generationMethod})"

end Eurisko

-- Test command
open Lean Elab Command

-- Run with default config
elab "#run_eurisko " n:num : command => do
  let n := n.getNat
  liftTermElabM do
    let _ ← Eurisko.runDiscovery n false
    pure ()

-- Run with mining
elab "#run_eurisko " n:num " with " "mining" : command => do
  let n := n.getNat
  liftTermElabM do
    let _ ← Eurisko.runDiscovery n true
    pure ()

-- Run the discovery system
#run_eurisko 5
