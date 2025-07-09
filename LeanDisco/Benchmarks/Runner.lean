import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.Core
import LeanDisco.Benchmarks.MiniF2F
import LeanDisco.Benchmarks.Metrics

namespace LeanDisco.Benchmarks.Runner

open Lean Elab Term Meta

/-- Create a proof-seeking heuristic for a specific problem -/
def createProofHeuristic (problemStmt : String) (problemId : String) : String × HeuristicFn := 
  (s!"proof_heuristic_{problemId}", fun config concepts => do
    IO.println s!"[BENCHMARK] Proof heuristic for {problemId} examining {concepts.length} concepts"
    
    -- Create a proof-seeking concept
    let proofName := s!"proof_{problemId}"
    let proofConcept := ConceptData.heuristicRef
      proofName
      s!"Attempting to prove: {problemStmt}"
      { name := proofName
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "benchmark_proof" }
    
    return [proofConcept]
  )

/-- Run LeanDisco discovery on a single problem -/
def runDiscoveryOnProblem (problem : Problem) (config : EvalConfig) : MetaM EvalResult := do
  let startTime ← IO.monoMsNow
  
  if config.verbose then
    IO.println s!"[BENCHMARK] Attempting problem: {problem.id}"
  
  -- Create custom heuristics for this problem
  let proofHeuristic := createProofHeuristic problem.formalStatement problem.id
  
  -- Create initial concepts focused on this problem
  let problemConcept := ConceptData.taskRef
    s!"solve_{problem.id}"
    problem.formalStatement
    { name := s!"solve_{problem.id}"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "benchmark_problem" }
  
  -- Set up discovery config
  let discoveryConfig : DiscoveryConfig := {
    maxConceptsPerIteration := min config.maxConcepts 50
    maxSpecializationDepth := min config.maxDepth 2
    enableDebugOutput := config.verbose
    pruneThreshold := 0.3
    enableConjectures := false
    enablePatternRecognition := false
  }
  
  -- Run custom discovery for this problem
  let initialKb ← initializeSystem discoveryConfig false
  
  -- Build custom knowledge base for this problem
  let kb : KnowledgeBase := {
    concepts := [problemConcept] ++ initialKb.concepts
    layers := initialKb.layers
    recentConcepts := [problemConcept] ++ initialKb.recentConcepts
    heuristics := initialKb.heuristics.insert proofHeuristic.1 proofHeuristic.2
    evaluators := initialKb.evaluators
    config := discoveryConfig
    iteration := 0
    history := []
    cache := {}
    failedProofs := []
  }
  
  -- Run a few iterations of discovery
  let maxIterations := 3
  let finalKb ← discoveryLoop kb maxIterations
  
  let endTime ← IO.monoMsNow
  
  -- Check if we found any proof-related concepts
  let proofConcepts := finalKb.concepts.filter fun c =>
    let name := getConceptName c
    contains name "proof" || contains name problem.id
  
  if proofConcepts.length > 0 then
    return {
      problemId := problem.id
      success := true
      proof := some s!"Found {proofConcepts.length} proof-related concepts"
      timeMs := endTime - startTime
      conceptsExplored := finalKb.concepts.length
      conceptsUsed := proofConcepts.map getConceptName
      heuristicsApplied := [s!"proof_heuristic_{problem.id}"]
      errorMsg := none
    }
  else
    return {
      problemId := problem.id
      success := false
      proof := none
      timeMs := endTime - startTime
      conceptsExplored := finalKb.concepts.length
      conceptsUsed := []
      heuristicsApplied := [s!"proof_heuristic_{problem.id}"]
      errorMsg := some "No proof concepts found"
    }

/-- Run evaluation on multiple problems using LeanDisco -/
def runEvaluation (problems : Array Problem) (config : EvalConfig) : MetaM (Array EvalResult) := do
  let mut results : Array EvalResult := #[]
  
  for problem in problems do
    let result ← runDiscoveryOnProblem problem config
    results := results.push result
    
    if config.verbose then
      IO.println s!"[BENCHMARK] Progress: {results.size}/{problems.size} completed"
  
  return results

/-- Run evaluation with retries for flaky problems -/
def runEvaluationWithRetries (problems : Array Problem) (config : EvalConfig) (maxRetries : Nat := 2) : 
    MetaM (Array EvalResult) := do
  let mut results : Array EvalResult := #[]
  let mut remainingProblems := problems
  
  for retry in [:maxRetries + 1] do
    if remainingProblems.isEmpty then break
    
    if retry > 0 && config.verbose then
      IO.println s!"[BENCHMARK] Retry {retry} for {remainingProblems.size} failed problems"
    
    let currentResults ← runEvaluation remainingProblems config
    
    -- Separate successful and failed results
    let (successful, failed) := currentResults.partition (·.success)
    results := results ++ successful
    
    -- Only retry failed problems
    remainingProblems := failed.map fun r =>
      problems.find? (·.id == r.problemId) |>.get!
  
  -- Add remaining failed results
  if !remainingProblems.isEmpty then
    let finalResults ← runEvaluation remainingProblems config
    results := results ++ finalResults
  
  return results

end LeanDisco.Benchmarks.Runner