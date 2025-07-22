import LeanDisco.Basic
import Lean

open LeanDisco Lean Meta

/-- Sample theorems NOT useful for MiniF2F problems -/
def nonMiniF2FBenchmarkTheorems : List (String × Expr × Expr) := [
  -- Category theory abstract theorems
  ("category_associativity", 
    Expr.forallE `C (Expr.const `Category [levelZero]) 
      (Expr.forallE `f (Expr.const `Morphism []) 
        (Expr.forallE `g (Expr.const `Morphism []) 
          (Expr.forallE `h (Expr.const `Morphism [])
            (Expr.app (Expr.app (Expr.const `Eq [levelOne])
              (Expr.app (Expr.app (Expr.const `compose []) 
                (Expr.app (Expr.app (Expr.const `compose []) (Expr.bvar 2)) (Expr.bvar 1))) 
                (Expr.bvar 0)))
              (Expr.app (Expr.app (Expr.const `compose []) (Expr.bvar 2))
                (Expr.app (Expr.app (Expr.const `compose []) (Expr.bvar 1)) (Expr.bvar 0))))
            .default)
          .default)
        .default)
      .default,
    Expr.const `sorry []),
    
  ("functor_composition_law",
    Expr.forallE `F (Expr.const `Functor [levelZero])
      (Expr.forallE `G (Expr.const `Functor [levelZero])
        (Expr.forallE `H (Expr.const `Functor [levelZero])
          (Expr.app (Expr.app (Expr.const `Eq [levelOne])
            (Expr.app (Expr.app (Expr.const `functor_compose []) 
              (Expr.app (Expr.app (Expr.const `functor_compose []) (Expr.bvar 2)) (Expr.bvar 1)))
              (Expr.bvar 0)))
            (Expr.app (Expr.app (Expr.const `functor_compose []) (Expr.bvar 2))
              (Expr.app (Expr.app (Expr.const `functor_compose []) (Expr.bvar 1)) (Expr.bvar 0))))
          .default)
        .default)
      .default,
    Expr.const `sorry []),
    
  -- Type theory theorems  
  ("type_universe_hierarchy",
    Expr.forallE `α (Expr.sort levelOne)
      (Expr.app (Expr.app (Expr.const `TypeInhabited [levelOne])
        (Expr.app (Expr.const `Type [levelOne]) (Expr.bvar 0)))
        (Expr.const `universe_polymorphism []))
      .default,
    Expr.const `sorry []),
    
  ("dependent_type_elimination",
    Expr.forallE `P (Expr.const `DependentType [levelZero])
      (Expr.forallE `x (Expr.const `term [])
        (Expr.app (Expr.const `eliminator [])
          (Expr.app (Expr.app (Expr.const `dependent_pair []) (Expr.bvar 1)) (Expr.bvar 0)))
        .default)
      .default,
    Expr.const `sorry []),
    
  -- Abstract algebra (non-numeric)
  ("group_homomorphism_kernel",
    Expr.forallE `φ (Expr.const `GroupHomomorphism [levelZero])
      (Expr.app (Expr.const `is_normal_subgroup [])
        (Expr.app (Expr.const `kernel []) (Expr.bvar 0)))
      .default,
    Expr.const `sorry []),
    
  ("ideal_quotient_ring",
    Expr.forallE `R (Expr.const `Ring [levelZero])
      (Expr.forallE `I (Expr.const `Ideal [levelZero])
        (Expr.app (Expr.const `is_ring [])
          (Expr.app (Expr.app (Expr.const `quotient []) (Expr.bvar 1)) (Expr.bvar 0)))
        .default)
      .default,
    Expr.const `sorry []),
    
  -- Logic and proof theory
  ("modal_logic_axiom_k",
    Expr.forallE `p (Expr.const `Proposition [])
      (Expr.forallE `q (Expr.const `Proposition [])
        (Expr.app (Expr.app (Expr.const `implies [])
          (Expr.app (Expr.const `necessary [])
            (Expr.app (Expr.app (Expr.const `implies []) (Expr.bvar 1)) (Expr.bvar 0))))
          (Expr.app (Expr.app (Expr.const `implies [])
            (Expr.app (Expr.const `necessary []) (Expr.bvar 1)))
            (Expr.app (Expr.const `necessary []) (Expr.bvar 0))))
        .default)
      .default,
    Expr.const `sorry []),
    
  ("intuitionistic_negation",
    Expr.forallE `A (Expr.const `Proposition [])
      (Expr.app (Expr.app (Expr.const `iff [])
        (Expr.app (Expr.const `not []) (Expr.bvar 0)))
        (Expr.app (Expr.app (Expr.const `implies []) (Expr.bvar 0))
          (Expr.const `absurd [])))
      .default,
    Expr.const `sorry []),
    
  -- Topology (abstract, non-metric)
  ("topological_space_closure_idempotent",
    Expr.forallE `X (Expr.const `TopologicalSpace [levelZero])
      (Expr.forallE `A (Expr.const `Set [levelZero])
        (Expr.app (Expr.app (Expr.const `Eq [levelOne])
          (Expr.app (Expr.const `closure [])
            (Expr.app (Expr.const `closure []) (Expr.bvar 0))))
          (Expr.app (Expr.const `closure []) (Expr.bvar 0)))
        .default)
      .default,
    Expr.const `sorry []),
    
  ("compact_hausdorff_normal",
    Expr.forallE `X (Expr.const `TopologicalSpace [levelZero])
      (Expr.app (Expr.app (Expr.const `implies [])
        (Expr.app (Expr.app (Expr.const `and [])
          (Expr.app (Expr.const `is_compact []) (Expr.bvar 0)))
          (Expr.app (Expr.const `is_hausdorff []) (Expr.bvar 0))))
        (Expr.app (Expr.const `is_normal []) (Expr.bvar 0)))
      .default,
    Expr.const `sorry []),
    
  -- Formal language theory
  ("context_free_pumping",
    Expr.forallE `L (Expr.const `Language [levelZero])
      (Expr.app (Expr.app (Expr.const `implies [])
        (Expr.app (Expr.const `is_context_free []) (Expr.bvar 0)))
        (Expr.app (Expr.const `satisfies_pumping_lemma []) (Expr.bvar 0)))
      .default,
    Expr.const `sorry []),
    
  -- Model theory
  ("compactness_theorem",
    Expr.forallE `T (Expr.const `Theory [levelZero])
      (Expr.app (Expr.app (Expr.const `iff [])
        (Expr.app (Expr.const `is_satisfiable []) (Expr.bvar 0)))
        (Expr.app (Expr.const `every_finite_subset_satisfiable []) (Expr.bvar 0)))
      .default,
    Expr.const `sorry []),
    
  -- Philosophical logic
  ("deontic_ought_implies_can",
    Expr.forallE `φ (Expr.const `Action [])
      (Expr.app (Expr.app (Expr.const `implies [])
        (Expr.app (Expr.const `obligatory []) (Expr.bvar 0)))
        (Expr.app (Expr.const `possible []) (Expr.bvar 0)))
      .default,
    Expr.const `sorry [])
]

/-- Run benchmark and display scores for non-MiniF2F theorems -/
def runNonMiniF2FBenchmark : MetaM Unit := do
  -- Initialize the system to get evaluators
  let kb ← initializeSystem {} false
  
  IO.println "=== Evaluator Benchmark on Non-MiniF2F-Relevant Theorems ===\n"
  
  for (name, stmt, proof) in nonMiniF2FBenchmarkTheorems do
    IO.println s!"Theorem: {name}"
    IO.println s!"Statement: {toString stmt}\n"
    
    -- Create a concept for this theorem
    let concept := ConceptData.theorem name stmt proof [] {
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

/-- Main entry point for the non-MiniF2F benchmark -/
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
    let _ ← (runNonMiniF2FBenchmark.run metaCtx metaState).run coreCtx { env } |>.toIO'
  catch e =>
    IO.eprintln s!"Error: {e}"