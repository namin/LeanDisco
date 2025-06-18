import LeanDisco.Basic

namespace LeanDisco.IncrementalSave

open Lean Meta Elab IO
open LeanDisco

/-- State information to save after each iteration -/
structure IterationState where
  iteration : Nat
  totalConcepts : Nat
  newConceptsThisIteration : Nat
  concepts : List String  -- Just names for now, full serialization is complex
  topConcepts : List (String × Float)  -- name and interestingness score
  patterns : List (String × String)  -- name and description
  conjectures : List (String × String)  -- name and statement (as string)
  theorems : List (String × String)  -- name and statement (as string)
  methods : List (String × Nat)  -- generation method and count

/-- Convert KnowledgeBase to a serializable state -/
def knowledgeBaseToState (kb : KnowledgeBase) (newConcepts : List ConceptData) : IterationState :=
  let conceptNames := kb.concepts.map getConceptName
  
  -- Get top concepts by interestingness
  let sorted := kb.concepts.toArray.qsort fun c1 c2 =>
    getInterestingness c1 > getInterestingness c2
  let topConcepts := (sorted.toList.take 10).map fun c =>
    (getConceptName c, getInterestingness c)
  
  -- Categorize concepts with details
  let patterns := kb.concepts.filterMap fun c => match c with
    | ConceptData.pattern name desc _ _ => some (name, desc)
    | _ => none
  
  let conjectures := kb.concepts.filterMap fun c => match c with
    | ConceptData.conjecture name stmt _ _ => some (name, toString stmt)
    | _ => none
  
  let theorems := kb.concepts.filterMap fun c => match c with
    | ConceptData.theorem name stmt _ _ _ => some (name, toString stmt)
    | _ => none
  
  -- Count by generation method
  let allMethods := ["seed", "mined", "application", "specialization", "conjecture", 
                     "pattern_recognition", "composition", "lemma_application",
                     "typeclass_specialization", "algebraic_conjecture", "concrete_instance"]
  let methods := allMethods.map fun method =>
    let count := kb.concepts.filter (fun c => (getConceptMetadata c).generationMethod == method) |>.length
    (method, count)
  
  { iteration := kb.iteration
    totalConcepts := kb.concepts.length
    newConceptsThisIteration := newConcepts.length
    concepts := conceptNames
    topConcepts := topConcepts
    patterns := patterns
    conjectures := conjectures
    theorems := theorems
    methods := methods.filter (·.2 > 0) }

/-- Format state as readable text -/
def formatIterationState (state : IterationState) : String :=
  let header := s!"=== ITERATION {state.iteration} COMPLETE ===\n"
  let summary := s!"Total Concepts: {state.totalConcepts} (+{state.newConceptsThisIteration} new)\n"
  
  let categoryInfo := String.join [
    s!"Patterns: {state.patterns.length}\n",
    s!"Conjectures: {state.conjectures.length}\n", 
    s!"Theorems: {state.theorems.length}\n"
  ]
  
  let topConceptsInfo := if state.topConcepts.length > 0 then
    let topList := state.topConcepts.map fun (name, score) =>
      s!"  - {name} (score: {score.toString})"
    s!"Top Concepts:\n" ++ String.intercalate "\n" topList ++ "\n"
  else ""
  
  let methodsInfo := if state.methods.length > 0 then
    let methodList := state.methods.map fun (method, count) =>
      s!"  {method}: {count}"
    s!"Generation Methods:\n" ++ String.intercalate "\n" methodList ++ "\n"
  else ""
  
  let recentPatterns := if state.patterns.length > 0 then
    let patternList := state.patterns.map fun (name, desc) =>
      s!"  - {name}: {desc}"
    s!"All Patterns ({state.patterns.length}):\n" ++ String.intercalate "\n" patternList ++ "\n"
  else ""
  
  let recentConjectures := if state.conjectures.length > 0 then
    let conjList := state.conjectures.map fun (name, stmt) =>
      s!"  - {name}\n    Statement: {stmt}"
    s!"All Conjectures ({state.conjectures.length}):\n" ++ String.intercalate "\n" conjList ++ "\n"
  else ""
  
  let recentTheorems := if state.theorems.length > 0 then
    let thmList := state.theorems.map fun (name, stmt) =>
      s!"  - {name}\n    Statement: {stmt}"
    s!"All Theorems ({state.theorems.length}):\n" ++ String.intercalate "\n" thmList ++ "\n"
  else ""
  
  header ++ summary ++ categoryInfo ++ topConceptsInfo ++ methodsInfo ++ recentPatterns ++ recentConjectures ++ recentTheorems ++ "\n"

/-- Save iteration state to file -/
def saveIterationState (state : IterationState) (basePath : String := "log/discovery") : IO Unit := do
  let timestamp := ← IO.monoMsNow
  
  -- Create log directory if it doesn't exist
  let _ ← IO.Process.output { cmd := "mkdir", args := #["-p", "log"] }
  
  -- Save formatted state
  let filename := s!"{basePath}_iteration_{state.iteration}.txt"
  let content := formatIterationState state
  IO.FS.writeFile filename content
  
  -- Also append to a cumulative log
  let cumulativeFile := s!"{basePath}_full.txt" 
  let separator := String.replicate 80 '=' ++ "\n"
  -- Read existing content and append
  let existingContent ← try
    IO.FS.readFile cumulativeFile
  catch _ =>
    pure ""
  IO.FS.writeFile cumulativeFile (existingContent ++ content ++ separator)
  
  IO.println s!"[SAVE] Iteration {state.iteration} state saved to {filename}"

/-- Enhanced discovery loop with intermediate saving -/
partial def discoveryLoopWithSaving 
    (kb : KnowledgeBase) 
    (maxIterations : Nat) 
    (saveBasePath : String := "log/discovery") : MetaM KnowledgeBase := do
  
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
    IO.println s!"{evaluatedConcepts.length} new concepts discovered this iteration"

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

  -- Update concept layers with new discoveries (simplified for now)
  let newConceptsForLayers := evaluatedConcepts ++ provenConjectures
  let updatedLayers : ConceptLayers := {
    foundational := kb.layers.foundational
    historical := kb.layers.historical ++ kb.layers.recent
    recent := newConceptsForLayers
    current := newConceptsForLayers
  }

  let newKb : KnowledgeBase := {
    concepts := remainingConcepts ++ provenConjectures
    layers := updatedLayers
    recentConcepts := evaluatedConcepts ++ provenConjectures
    heuristics := kb.heuristics
    evaluators := kb.evaluators
    config := kb.config
    iteration := kb.iteration + 1
    history := kb.history ++ [(kb.iteration, (evaluatedConcepts ++ provenConjectures).map getConceptName)]
    cache := newCache
    failedProofs := kb.failedProofs
  }

  -- SAVE INTERMEDIATE STATE
  let state := knowledgeBaseToState newKb (evaluatedConcepts ++ provenConjectures)
  saveIterationState state saveBasePath

  discoveryLoopWithSaving newKb maxIterations saveBasePath

/-- Enhanced runDiscoveryCustom with saving -/
def runDiscoveryCustomWithSaving
    (description : String)
    (initialConcepts : List ConceptData)
    (customHeuristics : List (String × HeuristicFn))
    (customEvaluators : List (String × EvaluationFn))
    (maxIterations : Nat := 10) 
    (useMining : Bool := false) 
    (config : DiscoveryConfig := {})
    (saveBasePath : String := "log/discovery") : MetaM Unit := do
  
  IO.println s!"=== Starting {description}Discovery System with Incremental Saving ==="
  IO.println s!"Config: maxDepth={config.maxSpecializationDepth}, maxPerIter={config.maxConceptsPerIteration}"
  IO.println s!"Features: conjectures={config.enableConjectures}, patterns={config.enablePatternRecognition}"
  IO.println s!"Mining mode: {if useMining then "ON" else "OFF"}"
  IO.println s!"Saving to: {saveBasePath}_*.txt"
  IO.println "Initializing with mathematical seed concepts..."

  let kb0 ← initializeSystem config useMining

  -- Build heuristics registry
  let mut heuristics : HeuristicRegistry := kb0.heuristics

  -- Add all heuristics (custom ones override standard if same name)
  for (name, fn) in customHeuristics do
    heuristics := heuristics.insert name fn

  -- Build evaluators registry
  let mut evaluators : EvaluationRegistry := kb0.evaluators

  -- Add all evaluators (custom ones override standard if same name)
  for (name, fn) in customEvaluators do
    evaluators := evaluators.insert name fn

  -- Create heuristic reference concepts
  let heuristicRefs := customHeuristics.map fun (name, _) =>
    ConceptData.heuristicRef name s!"Custom heuristic: {name}"
      { name := name
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "initial" }

  -- Create knowledge base
  let kb : KnowledgeBase := {
    concepts := initialConcepts ++ kb0.concepts ++ heuristicRefs
    layers := kb0.layers
    recentConcepts := initialConcepts ++ kb0.concepts
    heuristics := heuristics
    evaluators := evaluators
    config := kb0.config
    iteration := kb0.iteration
    history := kb0.history
    cache := kb0.cache
    failedProofs := kb0.failedProofs
  }

  IO.println s!"\nInitial concepts ({kb.concepts.length}):"
  showConceptStats kb.concepts

  -- Save initial state
  let initialState := knowledgeBaseToState kb []
  saveIterationState initialState saveBasePath

  let finalKb ← discoveryLoopWithSaving kb maxIterations saveBasePath

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

  -- Save final summary
  let finalState := knowledgeBaseToState finalKb []
  let methodLines := String.intercalate "\n" (finalState.methods.map fun (method, count) => s!"  {method}: {count}")
  let summaryContent := s!"FINAL DISCOVERY SUMMARY\n=======================\nTotal Iterations: {finalKb.iteration}\nFinal Concept Count: {finalKb.concepts.length}\nPatterns Found: {patterns.length}\nTop Scoring Concepts: {finalState.topConcepts.take 5}\n\nGeneration Method Distribution:\n{methodLines}\n"
  IO.FS.writeFile (saveBasePath ++ "_final_summary.txt") summaryContent
  IO.println s!"Final summary saved to {saveBasePath}_final_summary.txt"

end LeanDisco.IncrementalSave