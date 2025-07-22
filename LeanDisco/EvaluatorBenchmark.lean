import LeanDisco.Basic
import Lean

open LeanDisco Lean Meta

/-- Sample theorems commonly used in MiniF2F solutions -/
def benchmarkTheorems : List (String × Expr × Expr) := [
  -- Inequality theorems
  ("triangle_inequality", 
    Expr.forallE `a (Expr.const `Real []) 
      (Expr.forallE `b (Expr.const `Real []) 
        (Expr.app (Expr.app (Expr.const `LE.le [levelZero]) 
          (Expr.app (Expr.const `abs []) (Expr.app (Expr.app (Expr.const `Add.add [levelZero]) (Expr.bvar 1)) (Expr.bvar 0))))
          (Expr.app (Expr.app (Expr.const `Add.add [levelZero]) 
            (Expr.app (Expr.const `abs []) (Expr.bvar 1)))
            (Expr.app (Expr.const `abs []) (Expr.bvar 0))))
        .default)
      .default),
    Expr.const `sorry []),
    
  ("am_gm_inequality",
    Expr.forallE `a (Expr.const `Real [])
      (Expr.forallE `b (Expr.const `Real [])
        (Expr.app (Expr.app (Expr.const `LE.le [levelZero])
          (Expr.app (Expr.const `sqrt []) 
            (Expr.app (Expr.app (Expr.const `Mul.mul [levelZero]) (Expr.bvar 1)) (Expr.bvar 0))))
          (Expr.app (Expr.app (Expr.const `Div.div [levelZero])
            (Expr.app (Expr.app (Expr.const `Add.add [levelZero]) (Expr.bvar 1)) (Expr.bvar 0)))
            (Expr.const `two [])))
        .default)
      .default),
    Expr.const `sorry []),
    
  -- Number theory theorems  
  ("prime_factorization_unique",
    Expr.forallE `n (Expr.const `Nat [])
      (Expr.app (Expr.app (Expr.const `Exists [levelZero]) 
        (Expr.const `List [levelZero]))
        (Expr.const `unique_prime_factorization []))
      .default,
    Expr.const `sorry []),
    
  ("gcd_lcm_product",
    Expr.forallE `a (Expr.const `Nat [])
      (Expr.forallE `b (Expr.const `Nat [])
        (Expr.app (Expr.app (Expr.const `Eq [levelOne])
          (Expr.app (Expr.app (Expr.const `Mul.mul [levelZero]) 
            (Expr.app (Expr.app (Expr.const `gcd []) (Expr.bvar 1)) (Expr.bvar 0)))
            (Expr.app (Expr.app (Expr.const `lcm []) (Expr.bvar 1)) (Expr.bvar 0))))
          (Expr.app (Expr.app (Expr.const `Mul.mul [levelZero]) (Expr.bvar 1)) (Expr.bvar 0)))
        .default)
      .default,
    Expr.const `sorry []),
    
  -- Polynomial theorems
  ("polynomial_degree_sum",
    Expr.forallE `p (Expr.const `Polynomial [levelZero])
      (Expr.forallE `q (Expr.const `Polynomial [levelZero])
        (Expr.app (Expr.app (Expr.const `LE.le [levelZero])
          (Expr.app (Expr.const `degree []) 
            (Expr.app (Expr.app (Expr.const `Add.add [levelZero]) (Expr.bvar 1)) (Expr.bvar 0))))
          (Expr.app (Expr.app (Expr.const `max []) 
            (Expr.app (Expr.const `degree []) (Expr.bvar 1)))
            (Expr.app (Expr.const `degree []) (Expr.bvar 0))))
        .default)
      .default,
    Expr.const `sorry []),
    
  -- Combinatorial theorem
  ("binomial_sum_2n",
    Expr.forallE `n (Expr.const `Nat [])
      (Expr.app (Expr.app (Expr.const `Eq [levelOne])
        (Expr.app (Expr.const `sum_binomial_coefficients []) (Expr.bvar 0)))
        (Expr.app (Expr.app (Expr.const `Pow.pow [levelZero]) 
          (Expr.const `two [])) (Expr.bvar 0)))
      .default,
    Expr.const `sorry []),
    
  -- Simple theorem (for comparison)
  ("zero_add",
    Expr.forallE `a (Expr.const `Nat [])
      (Expr.app (Expr.app (Expr.const `Eq [levelOne])
        (Expr.app (Expr.app (Expr.const `Add.add [levelZero]) (Expr.const `zero [])) (Expr.bvar 0)))
        (Expr.bvar 0))
      .default,
    Expr.const `sorry []),
    
  -- Complex theorem (for comparison)  
  ("very_complex_theorem",
    Expr.forallE `f (Expr.const `ContinuousFunction [levelZero])
      (Expr.forallE `g (Expr.const `DifferentiableFunction [levelZero])
        (Expr.forallE `h (Expr.const `IntegrableFunction [levelZero])
          (Expr.app (Expr.const `exists_unique_fixed_point [])
            (Expr.app (Expr.app (Expr.app (Expr.const `compose [levelZero]) 
              (Expr.bvar 2)) (Expr.bvar 1)) (Expr.bvar 0)))
          .default)
        .default)
      .default,
    Expr.const `sorry [])
]

/-- Run benchmark and display scores -/
def runBenchmark : MetaM Unit := do
  -- Initialize the system to get evaluators
  let kb ← initializeSystem {} false
  
  IO.println "=== Evaluator Benchmark on MiniF2F-Relevant Theorems ===\n"
  
  for (name, stmt, proof) in benchmarkTheorems do
    IO.println s!"Theorem: {name}"
    IO.println s!"Statement: {toString stmt}\n"
    
    -- Create a concept for this theorem
    let concept := ConceptData.theorem name stmt proof "benchmark" {
      name := name
      created := 0
      parent := none
      interestingness := 0.5
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "benchmark"
    }
    
    let concepts := [concept]
    
    -- Evaluate with each evaluator
    IO.println "Scores:"
    
    -- Complexity evaluator
    if let some complexityFn := kb.evaluators.find? "complexity" then
      let complexityScore ← complexityFn concepts
      IO.println s!"  Complexity:         {complexityScore}"
    
    -- Novelty evaluator  
    if let some noveltyFn := kb.evaluators.find? "novelty" then
      let noveltyScore ← noveltyFn concepts
      IO.println s!"  Novelty:            {noveltyScore}"
    
    -- Pattern importance evaluator
    if let some patternFn := kb.evaluators.find? "pattern_importance" then
      let patternScore ← patternFn concepts
      IO.println s!"  Pattern Importance: {patternScore}"
    
    -- MiniF2F evaluator
    if let some miniF2FFn := kb.evaluators.find? "minif2f" then
      let miniF2FScore ← miniF2FFn concepts
      IO.println s!"  MiniF2F:            {miniF2FScore}"
    
    IO.println ""

/-- Main entry point for the benchmark -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  
  let env ← importModules [{ module := `Init : Import }] {}
  
  let coreCtx : Core.Context := {
    fileName := "<benchmark>"
    fileMap := FileMap.ofString ""
  }
  
  let metaCtx : Meta.Context := {}
  let metaState : Meta.State := {}
  
  match ← (runBenchmark.run metaCtx metaState).run coreCtx { env } with
  | .ok _ _ => pure ()
  | .error e _ => throw $ IO.userError s!"Error: {e.toMessageData.toString}"