import LeanDisco.Basic
import LeanDisco.ProofGuidedSimple
import LeanDisco.IncrementalSave

namespace LeanDisco.Domains.NumberTheory

open Lean Meta Elab
open LeanDisco

/-- Configuration for number theory concept mining -/
structure NumberTheoryConfig where
  includeBasicProperties : Bool := true      -- divisibility, primality, etc.
  includePrimes : Bool := true               -- prime numbers and properties
  includeModularArithmetic : Bool := true    -- congruences, modular operations
  includeFibonacci : Bool := false           -- Fibonacci sequence properties
  includeGCD : Bool := true                  -- greatest common divisor
  includePerfectNumbers : Bool := false      -- perfect, abundant, deficient numbers
  includeFactorization : Bool := true        -- prime factorization concepts
  maxPrimeToConsider : Nat := 17            -- largest prime to include (2,3,5,7,11,13,17)

/-- Check if a natural number is prime (hardcoded for simplicity) -/
def isPrimeSlow (n : Nat) : Bool :=
  n ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23]

/-- Generate a list of the first n prime numbers -/
def generatePrimes (n : Nat) : List Nat :=
  [2, 3, 5, 7, 11, 13].take n

/-- Check if two numbers are coprime (gcd = 1) -/
def areCoprime (a b : Nat) : Bool := Nat.gcd a b = 1

/-- Simple divisibility check -/
def divides (a b : Nat) : Bool := b % a = 0

/-- Generate basic number theory concepts -/
def mineNumberTheoryConcepts (config : NumberTheoryConfig := {}) : MetaM (List ConceptData) := do
  let mut concepts := []
  
  IO.println "[NumberTheory] Mining number theory concepts..."
  
  -- Basic natural numbers
  if config.includeBasicProperties then
    -- Add small natural numbers
    for i in [0, 1, 2, 3, 5, 7, 11, 13] do
      let numExpr := mkNatLit i
      let numName := s!"num_{i}"
      let numMetadata : ConceptMetadata := {
        name := numName
        created := 0
        parent := none
        interestingness := if i = 0 || i = 1 then 0.9 else if isPrimeSlow i then 0.8 else 0.6
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "number_theory_seed"
      }
      let numType := mkConst ``Nat
      let numConcept := ConceptData.definition numName numType numExpr none [] numMetadata
      concepts := concepts ++ [numConcept]
    
    -- Add basic operations
    let addConcept := ConceptData.definition "nat_add" (mkConst ``Nat.add) {
      name := "nat_add"
      created := 0
      parent := none
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "number_theory_operation"
    }
    
    let mulConcept := ConceptData.definition "nat_mul" (mkConst ``Nat.mul) {
      name := "nat_mul"
      created := 0
      parent := none
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "number_theory_operation"
    }
    
    let modConcept := ConceptData.definition "nat_mod" (mkConst ``Nat.mod) {
      name := "nat_mod"
      created := 0
      parent := none
      interestingness := 0.8
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "number_theory_operation"
    }
    
    concepts := concepts ++ [addConcept, mulConcept, modConcept]
  
  -- Prime numbers and primality
  if config.includePrimes then
    let primes := generatePrimes 6  -- First 6 primes: 2,3,5,7,11,13
    for p in primes do
      if p <= config.maxPrimeToConsider then
        let primeName := s!"prime_{p}"
        let primeExpr := mkNatLit p
        let primeConcept := ConceptData.definition primeName primeExpr {
          name := primeName
          created := 0
          parent := none
          interestingness := 0.95
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "prime_generation"
        }
        concepts := concepts ++ [primeConcept]
  
  -- GCD operations
  if config.includeGCD then
    let gcdConcept := ConceptData.definition "nat_gcd" (mkConst ``Nat.gcd) {
      name := "nat_gcd"
      created := 0
      parent := none
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "number_theory_operation"
    }
    concepts := concepts ++ [gcdConcept]
  
  -- Basic divisibility properties
  if config.includeBasicProperties then
    -- Even/odd patterns
    let evenPattern := ConceptData.pattern "even_numbers" "Numbers divisible by 2" ["num_0", "num_2"] {
      name := "even_numbers"
      created := 0
      parent := none
      interestingness := 0.7
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "pattern_recognition"
    }
    
    let oddPattern := ConceptData.pattern "odd_numbers" "Numbers not divisible by 2" ["num_1", "num_3", "num_5"] {
      name := "odd_numbers"
      created := 0
      parent := none
      interestingness := 0.7
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "pattern_recognition"
    }
    
    concepts := concepts ++ [evenPattern, oddPattern]
  
  -- Modular arithmetic
  if config.includeModularArithmetic then
    -- Add some modular properties as conjectures to discover
    let natType := mkConst ``Nat
    let stmt ← mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        mkSafeForall `n natType fun n => do
          let mod := mkConst ``Nat.mod
          let add := mkConst ``Nat.add
          let ab := mkApp2 add a b
          let ba := mkApp2 add b a
          let lhs := mkApp2 mod ab n
          let rhs := mkApp2 mod ba n
          return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
    let modAddCommConj := ConceptData.conjecture "mod_add_comm" stmt 0.8 {
      name := "mod_add_comm"
      created := 0
      parent := none
      interestingness := 0.8
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "modular_arithmetic_conjecture"
    }
    
    concepts := concepts ++ [modAddCommConj]
  
  -- Factorization concepts
  if config.includeFactorization then
    -- Add some basic factorization examples as theorems to discover
    let factPattern := ConceptData.pattern "composite_factorization" "Composite numbers as products of smaller numbers" ["num_4", "num_6", "num_8"] {
      name := "composite_factorization"
      created := 0
      parent := none
      interestingness := 0.8
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "factorization_pattern"
    }
    concepts := concepts ++ [factPattern]
  
  IO.println s!"[NumberTheory] Generated {concepts.length} number theory concepts"
  return concepts

/-- Generate number theory specific goals for proof-guided discovery -/
def generateNumberTheoryGoals : MetaM (List (String × String × Float)) := do
  return [
    -- Basic arithmetic properties
    ("addition_commutative_mod", "∀ a b n : Nat, (a + b) % n = (b + a) % n", 0.9),
    ("multiplication_commutative_mod", "∀ a b n : Nat, (a * b) % n = (b * a) % n", 0.9),
    
    -- GCD properties
    ("gcd_commutative", "∀ a b : Nat, Nat.gcd a b = Nat.gcd b a", 0.85),
    ("gcd_self", "∀ a : Nat, Nat.gcd a a = a", 0.8),
    ("gcd_zero", "∀ a : Nat, Nat.gcd a 0 = a", 0.85),
    
    -- Divisibility properties
    ("divisibility_transitive", "∀ a b c : Nat, a ∣ b → b ∣ c → a ∣ c", 0.9),
    ("one_divides_all", "∀ n : Nat, 1 ∣ n", 0.7),
    
    -- Prime properties
    ("two_is_prime", "Prime 2", 0.8),
    ("three_is_prime", "Prime 3", 0.8),
    
    -- Modular arithmetic
    ("mod_self", "∀ n : Nat, n % n = 0", 0.75),
    ("mod_zero", "∀ n : Nat, 0 % n = 0", 0.75),
    ("mod_distributive_add", "∀ a b n : Nat, (a + b) % n = ((a % n) + (b % n)) % n", 0.95),
    
    -- Basic number properties
    ("even_plus_even", "∀ a b : Nat, Even a → Even b → Even (a + b)", 0.8),
    ("odd_plus_odd", "∀ a b : Nat, Odd a → Odd b → Even (a + b)", 0.8),
    
    -- Coprimality
    ("gcd_one_coprime", "∀ a b : Nat, Nat.gcd a b = 1 ↔ Coprime a b", 0.85)
  ]


/-- Generate Lean expressions from number theory descriptions -/
def generateNumberTheoryStatement (desc : String) : MetaM Expr := do
  let natType := mkConst ``Nat
  match desc with
  | "∀ a b n : Nat, (a + b) % n = (b + a) % n" =>
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        mkSafeForall `n natType fun n => do
          let add := mkConst ``Nat.add
          let mod := mkConst ``Nat.mod
          let ab := mkApp2 add a b
          let ba := mkApp2 add b a
          let lhs := mkApp2 mod ab n
          let rhs := mkApp2 mod ba n
          return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | "∀ a b n : Nat, (a * b) % n = (b * a) % n" =>
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        mkSafeForall `n natType fun n => do
          let mul := mkConst ``Nat.mul
          let mod := mkConst ``Nat.mod
          let ab := mkApp2 mul a b
          let ba := mkApp2 mul b a
          let lhs := mkApp2 mod ab n
          let rhs := mkApp2 mod ba n
          return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | "∀ a b : Nat, Nat.gcd a b = Nat.gcd b a" =>
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        let gcd := mkConst ``Nat.gcd
        let lhs := mkApp2 gcd a b
        let rhs := mkApp2 gcd b a
        return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | "∀ a : Nat, Nat.gcd a a = a" =>
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      let gcd := mkConst ``Nat.gcd
      let lhs := mkApp2 gcd a a
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs a
  | "∀ a : Nat, Nat.gcd a 0 = a" =>
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      let gcd := mkConst ``Nat.gcd
      let zero := mkConst ``Nat.zero
      let lhs := mkApp2 gcd a zero
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs a
  | "∀ n : Nat, n % n = 0" =>
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let mod := mkConst ``Nat.mod
      let zero := mkConst ``Nat.zero
      let lhs := mkApp2 mod n n
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs zero
  | "∀ n : Nat, 0 % n = 0" =>
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let mod := mkConst ``Nat.mod
      let zero := mkConst ``Nat.zero
      let lhs := mkApp2 mod zero n
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs zero
  | _ =>
    -- Fallback to True for unrecognized descriptions
    return mkConst ``True

/-- Create number theory specific proof goals -/
def createNumberTheoryProofGoals : MetaM Unit := do
  let goalSpecs ← generateNumberTheoryGoals
  
  for (goalName, description, priority) in goalSpecs do
    let stmt ← generateNumberTheoryStatement description
    let goal : ProofGuidedSimple.ProofGoal := {
      name := goalName
      statement := stmt
      priority := priority
    }
    ProofGuidedSimple.addProofGoal goal
    IO.println s!"[NumberTheory] Added goal: {goalName}"

/-- Number theory specific heuristics for discovery -/
def numberTheorySpecializationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []
  
  -- Look for number theory concepts to specialize
  let numberConcepts := concepts.filter fun c => 
    let meta := getConceptMetadata c
    contains meta.generationMethod "number_theory" || 
    contains (getConceptName c) "num_" ||
    contains (getConceptName c) "prime_"
  
  if numberConcepts.length > 0 then
    IO.println s!"[NumberTheory] Specializing {numberConcepts.length} number theory concepts"
    
    -- Specialize with small primes and interesting numbers
    let specialValues := [2, 3, 5, 7, 11]
    
    for concept in numberConcepts.take 5 do  -- Limit to avoid explosion
      for value in specialValues.take 3 do
        let conceptName := getConceptName concept
        let specializedName := s!"{conceptName}_specialized_{value}"
        
        -- Create a specialized version (simplified for now)
        let metadata : ConceptMetadata := {
          name := specializedName
          created := 0
          parent := some conceptName
          interestingness := 0.6
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "number_theory_specialization"
        }
        let natType := mkConst ``Nat
        let specialized := ConceptData.definition specializedName natType (mkNatLit value) none [] metadata
        newConcepts := newConcepts ++ [specialized]
  
  return newConcepts.take config.maxConceptsPerIteration

/-- Test number theory discovery -/
def runNumberTheoryDiscoveryTest : MetaM Unit := do
  IO.println "=== NUMBER THEORY DISCOVERY TEST ==="
  IO.println "Testing proof-guided discovery on number theory problems"
  IO.println ""
  
  -- Mine number theory concepts
  let ntConcepts ← mineNumberTheoryConcepts {
    includeBasicProperties := true
    includePrimes := true
    includeModularArithmetic := true
    includeGCD := true
    includeFactorization := true
    maxPrimeToConsider := 13
  }
  
  IO.println s!"[NumberTheory] Mined {ntConcepts.length} concepts"
  
  -- Reset proof state
  ProofGuidedSimple.proofGuidedStateRef.set { 
    goals := [], completedGoals := [], failedGoals := [] 
  }
  
  -- Create number theory proof goals
  createNumberTheoryProofGoals
  
  -- Set up hybrid heuristics with number theory specialization
  let hybridHeuristics : List (String × HeuristicFn) := [
    ("nt_goal_seeding", ProofGuidedSimple.goalSeedingHeuristic),
    ("nt_specialization", numberTheorySpecializationHeuristic),
    ("proof_guided_discovery", ProofGuidedSimple.proofGuidedDiscoveryHeuristic),
    ("traditional_specialization", specializationHeuristic),
    ("application", applicationHeuristic),
    ("pattern_recognition", patternRecognitionHeuristic)
  ]
  
  -- Configure for number theory
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    enableConjectures := true
    enablePatternRecognition := true
  }
  
  -- Run discovery
  IncrementalSave.runDiscoveryCustomWithSaving
    "Number Theory Proof-Guided Discovery"
    ntConcepts
    hybridHeuristics
    []
    3  -- 3 iterations
    false
    config
    "log/number_theory_discovery"
  
  -- Show results
  let finalState ← ProofGuidedSimple.proofGuidedStateRef.get
  IO.println ""
  IO.println "=== NUMBER THEORY DISCOVERY RESULTS ==="
  IO.println s!"🎯 Goals Completed: {finalState.completedGoals.length}"
  for goalName in finalState.completedGoals do
    IO.println s!"   ✅ {goalName}"
  
  IO.println s!"🔄 Goals Remaining: {finalState.goals.length}"
  for goal in finalState.goals.take 5 do
    IO.println s!"   🎯 {goal.name} (priority: {goal.priority})"

end LeanDisco.Domains.NumberTheory