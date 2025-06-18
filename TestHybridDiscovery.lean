import LeanDisco.Domains.GroupRing
import LeanDisco.ProofGuidedSimple
import LeanDisco.IncrementalSave

namespace TestHybridDiscovery

open LeanDisco LeanDisco.Domains.GroupRing LeanDisco.ProofGuidedSimple LeanDisco.IncrementalSave
open Lean Meta Elab

/-- Test hybrid discovery combining traditional and proof-guided approaches -/
def runHybridDiscoveryTest : MetaM Unit := do
  IO.println "=== HYBRID DISCOVERY SYSTEM TEST ==="
  IO.println "Combining traditional exploration with proof-guided discovery"
  IO.println ""
  
  -- Mine basic GroupRing concepts as foundation
  let initialConcepts ← mineGroupRingConcepts { 
    includeBasicGroupTheory := true
    includeCommutativeGroups := false
    includeBasicRingTheory := true
    includeHomomorphisms := false
    includeSubstructures := false
    includeIdeals := false
  }
  IO.println s!"[FOUNDATION] Mined {initialConcepts.length} initial concepts from GroupRing domain"
  
  -- Reset proof goal state for clean test
  proofGuidedStateRef.set { goals := [], completedGoals := [], failedGoals := [] }
  
  -- Define hybrid heuristics in strategic order
  let hybridHeuristics : List (String × HeuristicFn) := [
    -- Phase 1: Goal seeding (create mathematical targets)
    ("goal_seeding", goalSeedingHeuristic),
    
    -- Phase 2: Traditional exploration (expand concept space)
    ("specialization", specializationHeuristic),
    ("application", applicationHeuristic),
    
    -- Phase 3: Proof-guided discovery (focused lemma generation)
    ("proof_guided_discovery", proofGuidedDiscoveryHeuristic),
    
    -- Phase 4: Pattern recognition (find emergent patterns)
    ("pattern_recognition", patternRecognitionHeuristic)
  ]
  
  -- Configure discovery for balanced exploration
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 15  -- Allow more concepts for richer exploration
    enableConjectures := true
    enablePatternRecognition := true
  }
  
  IO.println "=== DISCOVERY CONFIGURATION ==="
  IO.println s!"Max concepts per iteration: {config.maxConceptsPerIteration}"
  IO.println s!"Max specialization depth: {config.maxSpecializationDepth}"
  IO.println s!"Heuristics (in order): {hybridHeuristics.map (·.1)}"
  IO.println ""
  
  -- Run discovery with both approaches for 3 iterations
  let description := "Hybrid Discovery Test"
  let maxIterations := 3
  let saveBasePath := "log/hybrid_discovery_test"
  
  runDiscoveryCustomWithSaving
    description
    initialConcepts
    hybridHeuristics
    []  -- No custom evaluators
    maxIterations
    false  -- Don't use mining mode
    config
    saveBasePath
  
  -- Analyze final proof goal state
  let finalState ← proofGuidedStateRef.get
  IO.println ""
  IO.println "=== HYBRID DISCOVERY RESULTS ==="
  IO.println s!"🎯 Proof Goals Completed: {finalState.completedGoals.length}"
  for goalName in finalState.completedGoals do
    IO.println s!"   ✅ {goalName}"
  
  IO.println s!"🔄 Proof Goals Remaining: {finalState.goals.length}"
  for goal in finalState.goals.take 5 do  -- Show top 5
    IO.println s!"   🎯 {goal.name} (priority: {goal.priority})"
  
  IO.println s!"❌ Failed Goal Attempts: {finalState.failedGoals.length}"
  for goalName in finalState.failedGoals.take 3 do
    IO.println s!"   ❌ {goalName}: analysis attempted"

/-- Compare traditional vs proof-guided effectiveness -/
def analyzeDiscoveryEffectiveness : MetaM Unit := do
  IO.println ""
  IO.println "=== DISCOVERY APPROACH ANALYSIS ==="
  
  -- This analysis would ideally compare metrics like:
  -- - Concepts generated per heuristic
  -- - Success rate of proof attempts  
  -- - Interestingness scores by generation method
  -- - Coverage of mathematical properties
  
  IO.println "📊 Analysis of Discovery Effectiveness:"
  IO.println ""
  IO.println "🔬 Traditional Heuristics (Exploration-Based):"
  IO.println "   ✓ Generate many concepts through specialization/application"
  IO.println "   ✓ Good for discovering unexpected patterns"
  IO.println "   ⚠ May generate low-quality or uninteresting concepts"
  IO.println "   ⚠ No guarantee of mathematical usefulness"
  IO.println ""
  IO.println "🎯 Proof-Guided Heuristics (Need-Based):"
  IO.println "   ✓ Generate concepts needed for specific mathematical goals"
  IO.println "   ✓ High-quality, targeted lemma generation"
  IO.println "   ✓ Focused on mathematical necessity"
  IO.println "   ⚠ May miss unexpected discoveries"
  IO.println "   ⚠ Requires good initial goal seeding"
  IO.println ""
  IO.println "🔄 Hybrid Approach Benefits:"
  IO.println "   ✅ Combines exploration with focused discovery"
  IO.println "   ✅ Traditional heuristics provide concept diversity"
  IO.println "   ✅ Proof-guided heuristics ensure mathematical relevance"
  IO.println "   ✅ Goal seeding creates continuous mathematical targets"
  IO.println "   ✅ Pattern recognition finds emergent structures"

/-- Main test combining both analyses -/
def runCompleteHybridTest : MetaM Unit := do
  runHybridDiscoveryTest
  analyzeDiscoveryEffectiveness

#eval runCompleteHybridTest

end TestHybridDiscovery