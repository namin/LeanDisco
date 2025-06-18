import LeanDisco.Domains.GroupRing
import LeanDisco.ProofGuided
import LeanDisco.ProofGuidedHeuristics

namespace TestProofGuidedGroupRing

open LeanDisco LeanDisco.Domains.GroupRing LeanDisco.ProofGuided LeanDisco.ProofGuidedHeuristics
open Lean Meta Elab

/-- Test proof-guided discovery in the Group/Ring domain -/
def runProofGuidedGroupRingDiscovery
    (grConfig : GroupRingConfig := {})
    (discoConfig : DiscoveryConfig := {})
    (maxIterations : Nat := 10) : MetaM Unit := do
  
  IO.println "=== PROOF-GUIDED GROUP/RING DISCOVERY TEST ==="
  IO.println "This test demonstrates the new proof-guided discovery approach"
  IO.println "instead of random exploration.\n"
  
  -- Mine initial concepts from Group/Ring theory
  IO.println "[INIT] Mining Group/Ring concepts..."
  let initialConcepts ← mineGroupRingConcepts grConfig
  IO.println s!"[INIT] Mined {initialConcepts.length} concepts"
  
  -- Define proof-guided heuristics in priority order
  let proofGuidedHeuristics : List (String × HeuristicFn) := [
    ("proof_guided_discovery", proofGuidedDiscoveryHeuristic),
    ("goal_seeding", goalSeedingHeuristic), 
    ("lemma_discovery", lemmaDiscoveryHeuristic)
  ]
  
  -- Keep some traditional heuristics for comparison, but lower priority
  let traditionalHeuristics : List (String × HeuristicFn) := [
    ("specialization", HeuristicRegistry.get "specialization"),
    ("application", HeuristicRegistry.get "application"),
    ("conjecture_generation", HeuristicRegistry.get "conjecture_generation")
  ]
  
  let allHeuristics := proofGuidedHeuristics ++ traditionalHeuristics
  
  -- Reset proof-guided state for clean test
  proofGuidedStateRef.set { 
    goalQueue := ProofGoalQueue.empty, 
    completedGoals := [], 
    failedGoals := [] 
  }
  
  -- Configure for proof-guided discovery
  let proofGuidedConfig : DiscoveryConfig := {
    maxSpecializationDepth := 2  -- Reduced since we're more targeted
    maxConceptsPerIteration := 30  -- Smaller batches for quality
    enableConjectures := true
    enablePatternRecognition := true
  }
  
  let description := "Proof-Guided Group/Ring Theory "
  let saveBasePath := "log/proof_guided_groupring"
  
  -- Run the discovery with proof-guided heuristics
  runDiscoveryCustomWithSaving 
    description 
    initialConcepts 
    allHeuristics 
    []  -- No custom evaluators for now
    maxIterations 
    true  -- Use mining
    proofGuidedConfig 
    saveBasePath

-- Test with reduced scope for faster iteration
def runQuickProofGuidedTest : MetaM Unit := do
  IO.println "=== QUICK PROOF-GUIDED TEST (3 iterations) ==="
  
  runProofGuidedGroupRingDiscovery
    { includeBasicGroupTheory := true
      includeCommutativeGroups := false  -- Reduced scope
      includeBasicRingTheory := true
      includeHomomorphisms := false }    -- Reduced scope
    { maxSpecializationDepth := 2
      maxConceptsPerIteration := 20     -- Even smaller for quick test
      enableConjectures := true
      enablePatternRecognition := true }
    3  -- Just 3 iterations for quick feedback

-- Comparison test: run traditional vs proof-guided side by side
def runComparisonTest : MetaM Unit := do
  IO.println "=== COMPARISON: TRADITIONAL vs PROOF-GUIDED ==="
  
  let config := GroupRingConfig.mk true false true false false false
  let discoConfig := DiscoveryConfig.mk 2 25 true true
  
  -- Traditional approach (3 iterations)
  IO.println "\n--- TRADITIONAL APPROACH ---"
  runGroupRingDiscovery config discoConfig 3
  
  -- Wait a moment 
  IO.sleep 1000
  
  -- Proof-guided approach (3 iterations)  
  IO.println "\n--- PROOF-GUIDED APPROACH ---"
  runQuickProofGuidedTest

-- Demo the proof goal system specifically
def demoProofGoalSystem : MetaM Unit := do
  IO.println "=== PROOF GOAL SYSTEM DEMO ==="
  
  -- Reset state
  proofGuidedStateRef.set { 
    goalQueue := ProofGoalQueue.empty, 
    completedGoals := [], 
    failedGoals := [] 
  }
  
  -- Add some test goals manually
  let goal1 := createInterestingGoal "addition_commutative" "∀ n m : Nat, n + m = m + n" 0.9
  let goal2 := createInterestingGoal "multiplication_commutative" "∀ n m : Nat, n * m = m * n" 0.8
  let goal3 := createInterestingGoal "zero_identity" "∀ n : Nat, n + 0 = n" 0.7
  
  addProofGoal goal1
  addProofGoal goal2  
  addProofGoal goal3
  
  -- Show current goals
  let goals ← getCurrentProofGoals
  IO.println s!"Added {goals.length} test goals:"
  for goal in goals do
    IO.println s!"  - {goal.name} (priority: {goal.priority})"
  
  -- Test goal prioritization
  let kb := { concepts := [], layers := { foundational := [], historical := [], recent := [], current := [] }, 
              recentConcepts := [], heuristics := HeuristicRegistry.empty, evaluators := EvaluationRegistry.empty,
              config := {}, iteration := 0, history := [], cache := {}, failedProofs := [] }
  
  let prioritized := goals.qsort (fun g1 g2 => calculateGoalPriority g1 kb > calculateGoalPriority g2 kb)
  IO.println "\nPrioritized goals:"
  for goal in prioritized do
    let priority := calculateGoalPriority goal kb
    IO.println s!"  - {goal.name} (calculated priority: {priority})"

#eval runQuickProofGuidedTest

end TestProofGuidedGroupRing