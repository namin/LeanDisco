import LeanDisco

open LeanDisco
open LeanDisco.Domains.GroupRing

open Lean Meta Elab

def testDiscovery : MetaM Unit := do
  let grConfig : GroupRingConfig := {
    includeBasicGroupTheory := true
    includeCommutativeGroups := false
    includeBasicRingTheory := false
    includeHomomorphisms := false
    includeSubstructures := false
    includeIdeals := false
  }

  let discConfig : DiscoveryConfig := {
    maxSpecializationDepth := 3
    maxConceptsPerIteration := 30
    pruneThreshold := 0.1
    deduplicateConcepts := true
    canonicalizeConcepts := true
    filterInternalProofs := true
    enableConjectures := true
    enablePatternRecognition := true
  }

  -- Mine concepts
  let domainConcepts ← mineGroupRingConcepts grConfig
  let seedConcepts ← seedConcepts

  -- Build heuristics
  let mut heuristics : HeuristicRegistry := HeuristicRegistry.empty

  -- Add fixed heuristics first
  for (name, fn) in groupRingHeuristics do
    heuristics := heuristics.insert name fn

  -- Add standard heuristics
  heuristics := heuristics.insert "application" applicationHeuristic
  heuristics := heuristics.insert "lemma_application" lemmaApplicationHeuristic
  heuristics := heuristics.insert "pattern_recognition" patternRecognitionHeuristic
  heuristics := heuristics.insert "conjecture_generation" conjectureGenerationHeuristic

  -- Build evaluators
  let mut evaluators : EvaluationRegistry := EvaluationRegistry.empty
  evaluators := evaluators.insert "complexity" complexityTask
  evaluators := evaluators.insert "novelty" noveltyTask

  -- Create heuristic refs
  let heuristicRefs := groupRingHeuristics.map fun (name, _) =>
    ConceptData.heuristicRef name s!"Heuristic: {name}"
      { name := name, created := 0, parent := none, interestingness := 1.0,
        useCount := 0, successCount := 0, specializationDepth := 0,
        generationMethod := "initial" }

  let kb : KnowledgeBase := {
    concepts := seedConcepts ++ domainConcepts ++ heuristicRefs
    recentConcepts := seedConcepts ++ domainConcepts
    heuristics := heuristics
    evaluators := evaluators
    config := discConfig
    iteration := 0
    history := []
    cache := {}
    failedProofs := []
  }

  IO.println "=== Testing Fixed Discovery System ==="
  IO.println s!"Initial concepts: {kb.concepts.length}"

  -- Run discovery
  let finalKb ← discoveryLoop kb 3

  -- Show results
  IO.println "\n=== Results ==="

  -- Specialized theorems
  let specialized := finalKb.concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ meta =>
      meta.generationMethod == "typeclass_specialization"
    | _ => false

  IO.println s!"\nSpecialized Theorems ({specialized.length}):"
  for c in specialized do
    IO.println s!"  - {getConceptName c}"

  -- Applied theorems
  let applied := finalKb.concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ meta =>
      meta.generationMethod == "theorem_application"
    | _ => false

  IO.println s!"\nApplied Theorems ({applied.length}):"
  for c in applied.take 5 do
    IO.println s!"  - {getConceptName c}"

  -- Conjectures
  let conjectures := finalKb.concepts.filter fun c => match c with
    | ConceptData.conjecture _ _ _ _ => true
    | _ => false

  IO.println s!"\nConjectures ({conjectures.length}):"
  for c in conjectures do
    match c with
    | ConceptData.conjecture name _ ev _ =>
      IO.println s!"  - {name} (evidence: {ev})"
    | _ => pure ()

#eval testDiscovery
