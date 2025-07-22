import LeanDisco
import Lean

open LeanDisco Lean Meta

/-- Test evaluators on sample theorems -/
def benchmarkEvaluators : MetaM Unit := do
  IO.println "\n=== Evaluator Benchmark on MiniF2F-Relevant Theorems ===\n"
  
  -- Initialize system to get evaluators
  let kb ← initializeSystem {} false
  
  -- Create test theorems with different characteristics
  let testTheorems : List (String × String × List String × Float) := [
    -- High MiniF2F relevance theorems
    ("triangle_inequality", "Inequality theorem about triangle sides", ["inequality", "bound"], 0.9),
    ("am_gm_inequality", "Arithmetic-geometric mean inequality", ["inequality", "optimization"], 0.95),
    ("prime_factorization", "Every natural number has unique prime factorization", ["prime", "number_theory"], 0.8),
    ("binomial_sum", "Sum of binomial coefficients equals 2^n", ["combinatorial", "sum"], 0.85),
    ("polynomial_degree_bound", "Degree of polynomial sum bounded by max", ["polynomial", "bound"], 0.75),
    
    -- Medium relevance
    ("gcd_lcm_identity", "Product of gcd and lcm equals product", ["gcd", "lcm"], 0.6),
    ("function_composition", "Composition of injective functions", ["function", "injective"], 0.5),
    
    -- Low relevance  
    ("zero_add", "Zero is additive identity", ["basic", "addition"], 0.2),
    ("list_append_assoc", "List append is associative", ["list", "data_structure"], 0.1)
  ]
  
  IO.println "Test theorems (with expected MiniF2F relevance):"
  IO.println "------------------------------------------------"
  
  for (name, desc, keywords, expectedScore) in testTheorems do
    -- Create a mock theorem concept
    let concept := ConceptData.theorem name 
      (Expr.const `mock_statement [])
      (Expr.const `sorry [])
      keywords
      { name := name
        created := 0
        parent := none
        interestingness := 0.5
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "benchmark" }
    
    IO.println s!"\nTheorem: {name}"
    IO.println s!"Description: {desc}"
    IO.println s!"Keywords: {keywords}"
    IO.println s!"Expected MiniF2F relevance: {expectedScore}"
    
    -- Evaluate with each evaluator
    let concepts := [concept]
    
    let complexityScore ← match kb.evaluators.find? "complexity" with
      | some fn => fn concepts
      | none => pure 0.5
      
    let noveltyScore ← match kb.evaluators.find? "novelty" with  
      | some fn => fn concepts
      | none => pure 0.5
      
    let patternScore ← match kb.evaluators.find? "pattern_importance" with
      | some fn => fn concepts
      | none => pure 0.5
      
    let miniF2FScore ← match kb.evaluators.find? "minif2f" with
      | some fn => fn concepts
      | none => pure 0.5
    
    IO.println "Evaluator scores:"
    IO.println s!"  Complexity:         {complexityScore}"
    IO.println s!"  Novelty:            {noveltyScore}"
    IO.println s!"  Pattern Importance: {patternScore}"
    IO.println s!"  MiniF2F:            {miniF2FScore}"
    
    -- Show how MiniF2F differs from others
    let avgOtherScores := (complexityScore + noveltyScore + patternScore) / 3
    let miniF2FDiff := miniF2FScore - avgOtherScores
    IO.println s!"  MiniF2F vs avg others: {if miniF2FDiff > 0 then "+" else ""}{miniF2FDiff}"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  
  let env ← importModules #[{ module := `Init : Import }] {}
  
  let coreCtx : Core.Context := {
    fileName := "<benchmark>"
    fileMap := FileMap.ofString ""
  }
  
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  
  try
    let _ ← (benchmarkEvaluators.run metaCtx metaState).run coreCtx { env } |>.toIO'
  catch e =>
    IO.eprintln s!"Error: {e}"