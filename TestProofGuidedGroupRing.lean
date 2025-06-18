import LeanDisco.Domains.GroupRing
import LeanDisco.ProofGuidedSimple

namespace TestProofGuidedGroupRing

open LeanDisco LeanDisco.Domains.GroupRing LeanDisco.ProofGuidedSimple
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
  
  -- Define proof-guided heuristics 
  let proofGuidedHeuristics : List (String × HeuristicFn) := [
    ("goal_seeding", goalSeedingHeuristic), 
    ("proof_guided_discovery", proofGuidedDiscoveryHeuristic)
  ]
  
  -- Reset proof-guided state for clean test
  proofGuidedStateRef.set { 
    goals := [], 
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
  
  -- For now, just test the heuristics directly
  IO.println "\n=== TESTING PROOF-GUIDED HEURISTICS ==="
  
  -- Test goal seeding
  let goalConcepts ← goalSeedingHeuristic proofGuidedConfig initialConcepts
  IO.println s!"Goal seeding generated {goalConcepts.length} concepts"
  
  -- Test proof-guided discovery  
  let proofConcepts ← proofGuidedDiscoveryHeuristic proofGuidedConfig initialConcepts
  IO.println s!"Proof-guided discovery generated {proofConcepts.length} concepts"

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
  let discoConfig : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 25
    enableConjectures := true
    enablePatternRecognition := true
  }
  
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
    goals := [], 
    completedGoals := [], 
    failedGoals := [] 
  }
  
  -- Add some test goals manually
  let stmt1 ← generateProvableStatement "simple_true"
  let goal1 : ProofGoal := { name := "addition_commutative", statement := stmt1, priority := 0.9 }
  let stmt2 ← generateProvableStatement "zero_add"
  let goal2 : ProofGoal := { name := "zero_identity", statement := stmt2, priority := 0.7 }
  
  addProofGoal goal1
  addProofGoal goal2
  
  -- Show current goals
  let goals ← getCurrentProofGoals
  IO.println s!"Added {goals.length} test goals:"
  for goal in goals do
    IO.println s!"  - {goal.name} (priority: {goal.priority})"
  
  -- Test simple prioritization  
  let prioritized := goals.toArray.qsort (·.priority > ·.priority) |>.toList
  IO.println "\nPrioritized goals:"
  for goal in prioritized do
    IO.println s!"  - {goal.name} (priority: {goal.priority})"

/-- Test the proof capabilities -/
def testProofCapabilities : MetaM Unit := do
  IO.println "=== PROOF CAPABILITIES TEST ==="
  
  -- Reset state
  proofGuidedStateRef.set { 
    goals := [], 
    completedGoals := [], 
    failedGoals := [] 
  }
  
  IO.println "\n📋 Testing goal generation with mathematical statements..."
  
  -- Test goal seeding
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    enableConjectures := true
    enablePatternRecognition := true
  }
  
  let initialConcepts ← mineGroupRingConcepts { 
    includeBasicGroupTheory := true
    includeCommutativeGroups := false
    includeBasicRingTheory := true
    includeHomomorphisms := false
    includeSubstructures := false
    includeIdeals := false
  }
  
  -- Test goal seeding  
  let goalConcepts ← goalSeedingHeuristic config initialConcepts
  IO.println s!"✓ Goal seeding generated {goalConcepts.length} goal concepts"
  
  -- Test proof attempts with tactics
  IO.println "\n🔧 Testing proof tactics..."
  let proofConcepts ← proofGuidedDiscoveryHeuristic config initialConcepts
  IO.println s!"✓ Proof attempts generated {proofConcepts.length} concepts"
  
  -- Show final state
  let finalState ← proofGuidedStateRef.get
  IO.println s!"\n📊 Final State:"
  IO.println s!"  Active goals: {finalState.goals.length}"
  IO.println s!"  Completed goals: {finalState.completedGoals.length}"
  
  for completedGoal in finalState.completedGoals do
    IO.println s!"    ✓ {completedGoal}"

#eval testProofCapabilities

end TestProofGuidedGroupRing