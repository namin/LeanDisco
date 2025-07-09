import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.Core
import LeanDisco.Benchmarks.MiniF2F

namespace LeanDisco.Benchmarks.Runner

open Lean Elab Term Meta

/-- Convert benchmark problem to a proof goal -/
def problemToProofGoal (problem : Problem) : ProofGoal :=
  { statement := problem.formalStatement
    dependencies := []
    sorryCount := 0
    missingLemmas := []
    iteration := 0
  }

/-- Create a simple proof-finding heuristic for benchmarks -/
def benchmarkProofHeuristic (config : DiscoveryConfig) (concepts : List ConceptData) : MetaM (List ConceptData) := do
  -- This is a placeholder - in a real implementation, this would try various proof strategies
  return []

/-- Try to prove using LeanDisco's discovery system -/
def runDiscoveryOnProblem (problem : Problem) (config : EvalConfig) : 
    IO EvalResult := do
  let startTime ← IO.monoMsNow
  
  if config.verbose then
    IO.println s!"Attempting problem: {problem.id}"
  
  -- Run in MetaM context
  let coreM : CoreM EvalResult := do
    let metaM : MetaM EvalResult := do
      -- Create initial concepts for this problem
      let goalExpr ← try
        -- Parse the formal statement as an expression
        let env ← getEnv
        let stx ← match Parser.runParserCategory env `term problem.formalStatement with
          | .ok stx => pure stx
          | .error _ => throwError "Failed to parse problem statement"
        elabTerm stx none
      catch _ =>
        -- If parsing fails, create a dummy expression
        return (mkConst `True)
      
      let problemConcept := ConceptData.taskRef
        s!"prove_{problem.id}"
        problem.formalStatement
        (ConceptMetadata.mk
          s!"prove_{problem.id}"
          0
          none
          1.0  -- High priority
          0
          0
          0
          "benchmark_problem")
      
      -- Set up discovery configuration
      let discoveryConfig : DiscoveryConfig := {
        maxConceptsPerIteration := config.maxConcepts
        maxSpecializationDepth := config.maxDepth
        enableDebugOutput := config.verbose
        pruneThreshold := 0.05
        enableConjectures := false
      }
      
      -- Create knowledge base
      let kb : KnowledgeBase := {
        concepts := [problemConcept]
        layers := {}
        recentConcepts := [problemConcept]
        heuristics := HeuristicRegistry.empty.insert "benchmark_proof" benchmarkProofHeuristic
        evaluators := EvaluationRegistry.empty
        config := discoveryConfig
        failedProofs := []
        conceptCache := {}
        activeTasks := [problemToProofGoal problem]
      }
      
      -- Run a few iterations of discovery
      let finalKb ← (List.range 5).foldlM (fun kb _ => do
        -- Apply heuristics
        let newConcepts ← kb.heuristics.entries.foldlM (fun acc (_, heuristic) => do
          let generated ← heuristic kb.config kb.concepts
          return acc ++ generated
        ) []
        
        -- Check if we found a proof
        let proofFound := newConcepts.any fun c =>
          match c with
          | ConceptData.theorem n _ _ _ _ => n.contains problem.id
          | _ => false
        
        if proofFound then
          return kb  -- Stop if proof found
        else
          return { kb with 
            concepts := kb.concepts ++ newConcepts
            recentConcepts := newConcepts
          }
      ) kb
      
      let endTime ← IO.monoMsNow
      
      -- Check if we found a proof
      let proofConcept := finalKb.concepts.find? fun c =>
        match c with
        | ConceptData.theorem n _ _ _ _ => n.contains problem.id
        | _ => false
      
      match proofConcept with
      | some (ConceptData.theorem n _ _ _ _) =>
        return {
          problemId := problem.id
          success := true
          proof := some s!"Found proof: {n}"
          timeMs := endTime - startTime
          conceptsExplored := finalKb.concepts.length
          conceptsUsed := finalKb.concepts.map getConceptName
          heuristicsApplied := ["benchmark_proof"]
          errorMsg := none
        }
      | _ =>
        return {
          problemId := problem.id
          success := false
          proof := none
          timeMs := endTime - startTime
          conceptsExplored := finalKb.concepts.length
          conceptsUsed := []
          heuristicsApplied := ["benchmark_proof"]
          errorMsg := some "No proof found"
        }
    
    metaM.run'
  
  match ← coreM.toIO' with
  | .ok result => return result
  | .error e => 
    let endTime ← IO.monoMsNow
    return {
      problemId := problem.id
      success := false
      proof := none
      timeMs := endTime - startTime
      conceptsExplored := 0
      conceptsUsed := []
      heuristicsApplied := []
      errorMsg := some s!"Error: {e}"
    }

/-- Run evaluation on multiple problems -/
def runEvaluation (problems : Array Problem) (config : EvalConfig) : IO (Array EvalResult) := do
  if config.parallel then
    -- Parallel evaluation using tasks
    let tasks ← problems.mapM fun problem => do
      Task.spawn fun _ => runDiscoveryOnProblem problem config
    
    tasks.mapM Task.get
  else
    -- Sequential evaluation
    let mut results : Array EvalResult := #[]
    
    for problem in problems do
      let result ← runDiscoveryOnProblem problem config
      results := results.push result
      
      if config.verbose then
        IO.println s!"Progress: {results.size}/{problems.size} completed"
    
    return results

/-- Run evaluation with retries for flaky problems -/
def runEvaluationWithRetries (problems : Array Problem) (config : EvalConfig) (maxRetries : Nat := 2) : 
    IO (Array EvalResult) := do
  let mut results : Array EvalResult := #[]
  let mut remainingProblems := problems
  
  for retry in [:maxRetries + 1] do
    if remainingProblems.isEmpty then break
    
    if retry > 0 && config.verbose then
      IO.println s!"\nRetry {retry} for {remainingProblems.size} failed problems"
    
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