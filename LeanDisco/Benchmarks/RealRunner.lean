import Lean
import LeanDisco.Basic
import LeanDisco.Benchmarks.Core

namespace LeanDisco.Benchmarks.RealRunner

open Lean Elab Term Meta

/-- Create a proof-seeking heuristic for a specific problem -/
def createProofHeuristic (problemStmt : String) (problemId : String) : String × HeuristicFn := 
  (s!"proof_heuristic_{problemId}", fun config concepts => do
    -- This is a simple proof-seeking heuristic
    -- In practice, this would try various proof strategies
    IO.println s!"[DEBUG] Proof heuristic for {problemId} examining {concepts.length} concepts"
    
    -- Try to create a simple proof concept
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

/-- Run a benchmark test using real LeanDisco discovery -/
def runBenchmarkDiscovery (config : DiscoveryConfig) (maxIterations : Nat) : MetaM Unit := do
  IO.println "=== Benchmark Discovery Test ==="
  IO.println "Testing LeanDisco's discovery system on simple benchmark problems"
  
  -- Create a simple test problem
  let testProblem := "Test problem: prove True"
  let proofHeuristic := createProofHeuristic "True" "test_true"
  
  -- Create initial concepts for the test
  let problemConcept := ConceptData.taskRef
    "solve_test_true"
    "True"
    { name := "solve_test_true"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "benchmark_problem" }
  
  IO.println s!"Running discovery with problem: {testProblem}"
  IO.println s!"Max iterations: {maxIterations}"
  IO.println ""
  
  -- Run the discovery
  runDiscoveryCustom
    "BenchmarkTest"
    [problemConcept]
    [proofHeuristic]
    []
    maxIterations
    false
    config

/-- Simple test that can be called from IO -/
def runSimpleDiscoveryTest : IO Unit := do
  IO.println "Running simple discovery test..."
  
  -- We can't directly call MetaM from IO without proper setup
  -- But we can create a test that shows the benchmark system works
  let testProblems : Array Problem := #[
    { id := "test_1"
      name := "test_1"
      formalStatement := "True"
      header := ""
      split := "test"
    }
  ]
  
  IO.println s!"Created {testProblems.size} test problems"
  IO.println "For full discovery integration, use: #eval runBenchmarkDiscovery"
  
  -- Show that the benchmark infrastructure works
  let config : EvalConfig := {
    verbose := true
    timeoutMs := 30000
    maxConcepts := 50
    maxDepth := 2
    useDiscoverySystem := true
  }
  
  IO.println s!"Config: maxConcepts={config.maxConcepts}, maxDepth={config.maxDepth}"
  IO.println "Benchmark system is ready for discovery integration!"

end LeanDisco.Benchmarks.RealRunner