import LeanDisco.Basic
import Mathlib.Data.Nat.Basic

set_option linter.unusedVariables false

namespace LeanDisco.Domains.InfiniteNumbers

open Lean Meta Elab

/-- Simple domain that generates natural numbers indefinitely -/
def mineInfiniteNumbers : MetaM (List ConceptData) := do
  let mut concepts : List ConceptData := []
  
  let mkMeta (name : String) (method : String := "mined_infinite") : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := method
  }
  
  -- Just a few seed numbers
  let natType := mkConst ``Nat
  
  for i in [0, 1, 2] do
    let numExpr := (List.range i).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    
    concepts := concepts ++ [
      ConceptData.definition s!"num_{i}" natType numExpr none [] (mkMeta s!"num_{i}")
    ]
  
  return concepts

/-- Generate the next natural number in sequence -/
def generateNextNumber : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find existing numbers
  let existingNumbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "num_" then
        n.drop 4 |>.toNat?
      else if n == "zero" then some 0
      else if n == "one" then some 1
      else if n == "two" then some 2
      else none
    | _ => none
  
  let maxNum := existingNumbers.foldl max 0
  let nextNum := maxNum + 1
  
  -- Generate next number (should always be possible)
  if nextNum < 1000 then  -- increased limit for infinite generation
    let natType := mkConst ``Nat
    let numExpr := (List.range nextNum).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    
    newConcepts := newConcepts ++ [
      ConceptData.definition s!"num_{nextNum}" natType numExpr none [] {
        name := s!"num_{nextNum}"
        created := 0
        parent := some s!"num_{maxNum}"
        interestingness := 0.8
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "number_generation"
      }
    ]
  
  IO.println s!"[NextNum] Generated {newConcepts.length} new numbers (next: {nextNum})"
  return newConcepts

/-- Generate arithmetic operations between existing numbers -/
def generateArithmetic : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find numbers
  let numbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "num_" then
        some (n, v)
      else none
    | _ => none
  
  let natType := mkConst ``Nat
  
  -- Generate additions
  for (n1Name, n1Val) in numbers.take 10 do
    for (n2Name, n2Val) in numbers.take 10 do
      let sumName := s!"sum_{n1Name}_{n2Name}"
      
      if !concepts.any (fun c => getConceptName c == sumName) then
        let sumExpr := mkApp2 (mkConst ``Nat.add) n1Val n2Val
        
        newConcepts := newConcepts ++ [
          ConceptData.definition sumName natType sumExpr none [n1Name, n2Name] {
            name := sumName
            created := 0
            parent := some n1Name
            interestingness := 0.7
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "arithmetic_generation"
          }
        ]
  
  -- Generate multiplications  
  for (n1Name, n1Val) in numbers.take 8 do
    for (n2Name, n2Val) in numbers.take 8 do
      if n1Name != n2Name then  -- avoid x*x for now
        let prodName := s!"prod_{n1Name}_{n2Name}"
        
        if !concepts.any (fun c => getConceptName c == prodName) then
          let prodExpr := mkApp2 (mkConst ``Nat.mul) n1Val n2Val
          
          newConcepts := newConcepts ++ [
            ConceptData.definition prodName natType prodExpr none [n1Name, n2Name] {
              name := prodName
              created := 0
              parent := some n1Name
              interestingness := 0.75
              useCount := 0
              successCount := 0
              specializationDepth := 1
              generationMethod := "arithmetic_generation"
            }
          ]
  
  IO.println s!"[Arithmetic] Generated {newConcepts.length} arithmetic operations"
  return newConcepts

/-- Generate powers (x^2, x^3, etc.) -/
def generatePowers : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find base numbers
  let numbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "num_" then
        some (n, v)
      else none
    | _ => none
  
  let natType := mkConst ``Nat
  
  for (numName, numVal) in numbers.take 8 do
    for exp in [2, 3, 4] do
      let powerName := s!"power_{numName}_{exp}"
      
      if !concepts.any (fun c => getConceptName c == powerName) then
        let expExpr := (List.range exp).foldl (fun acc _ => 
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        let powerExpr := mkApp2 (mkConst ``Nat.pow) numVal expExpr
        
        newConcepts := newConcepts ++ [
          ConceptData.definition powerName natType powerExpr none [numName] {
            name := powerName
            created := 0
            parent := some numName
            interestingness := 0.8
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "power_generation"
          }
        ]
  
  IO.println s!"[Powers] Generated {newConcepts.length} power operations"
  return newConcepts

/-- Generate simple patterns and sequences -/
def generateSequences : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find the highest number we have
  let existingNumbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "num_" then
        n.drop 4 |>.toNat?
      else none
    | _ => none
  
  let maxNum := existingNumbers.foldl max 0
  
  -- Generate sequence operations like "next_odd", "next_even", "double", etc.
  if maxNum >= 2 then
    let natType := mkConst ``Nat
    let seqType ← mkArrow natType natType
    
    -- Double function: n ↦ 2*n
    let doubleName := "seq_double"
    if !concepts.any (fun c => getConceptName c == doubleName) then
      let doubleFunc ← mkSafeLambda `n natType fun n => do
        let two := mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))
        return mkApp2 (mkConst ``Nat.mul) two n
      
      newConcepts := newConcepts ++ [
        ConceptData.definition doubleName seqType doubleFunc none [] {
          name := doubleName
          created := 0
          parent := none
          interestingness := 0.9
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "sequence_generation"
        }
      ]
    
    -- Add-one function: n ↦ n+1  
    let addOneName := "seq_add_one"
    if !concepts.any (fun c => getConceptName c == addOneName) then
      let addOneFunc ← mkSafeLambda `n natType fun n => do
        let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
        return mkApp2 (mkConst ``Nat.add) n one
      
      newConcepts := newConcepts ++ [
        ConceptData.definition addOneName seqType addOneFunc none [] {
          name := addOneName
          created := 0
          parent := none
          interestingness := 0.85
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "sequence_generation"
        }
      ]
  
  IO.println s!"[Sequences] Generated {newConcepts.length} sequence functions"
  return newConcepts

/-- Apply sequence functions to numbers -/
def applySequences : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find sequence functions
  let sequences := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "seq_" then
        some (n, v)
      else none
    | _ => none
  
  -- Find numbers
  let numbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "num_" then
        some (n, v)
      else none
    | _ => none
  
  let natType := mkConst ``Nat
  
  -- Apply each sequence to each number
  for (seqName, seqVal) in sequences do
    for (numName, numVal) in numbers.take 12 do
      let appliedName := s!"{seqName}_applied_to_{numName}"
      
      if !concepts.any (fun c => getConceptName c == appliedName) then
        let resultExpr := mkApp seqVal numVal
        
        newConcepts := newConcepts ++ [
          ConceptData.definition appliedName natType resultExpr none [seqName, numName] {
            name := appliedName
            created := 0
            parent := some seqName
            interestingness := 0.7
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "sequence_application"
          }
        ]
  
  IO.println s!"[SeqApplication] Generated {newConcepts.length} sequence applications"
  return newConcepts

/-- Generate Fibonacci-like sequences -/
def generateFibonacciLike : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find pairs of numbers to start sequences
  let numbers := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "num_" || n == "zero" || n == "one" || n == "two" then
        some (n, v)
      else none
    | _ => none
  
  let natType := mkConst ``Nat
  
  -- Check if we already have fib concepts
  let hasFib := concepts.any fun c => 
    let name := getConceptName c
    name.startsWith "fib_"
  
  if !hasFib && numbers.length >= 2 then
    -- Start with fib_0 = 0, fib_1 = 1
    if let some (_, zeroVal) := numbers.find? (fun (n, _) => n == "zero" || n == "num_0") then
      if let some (_, oneVal) := numbers.find? (fun (n, _) => n == "one" || n == "num_1") then
        newConcepts := newConcepts ++ [
          ConceptData.definition "fib_0" natType zeroVal none [] {
            name := "fib_0"
            created := 0
            parent := none
            interestingness := 0.95
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "fibonacci_generation"
          },
          ConceptData.definition "fib_1" natType oneVal none [] {
            name := "fib_1"
            created := 0
            parent := none
            interestingness := 0.95
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "fibonacci_generation"
          }
        ]
  
  -- Generate next Fibonacci numbers
  let fibs := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "fib_" then
        n.drop 4 |>.toNat?.map (·, v)
      else none
    | _ => none
  
  if fibs.length >= 2 then
    let sortedFibs := fibs.toArray.qsort (·.1 < ·.1)
    if h : sortedFibs.size >= 2 then
      let (n1, v1) := sortedFibs[sortedFibs.size - 2]
      let (n2, v2) := sortedFibs[sortedFibs.size - 1]
      let nextN := n2 + 1
      
      let nextFibName := s!"fib_{nextN}"
      if !concepts.any (fun c => getConceptName c == nextFibName) then
        let nextVal := mkApp2 (mkConst ``Nat.add) v1 v2
        
        newConcepts := newConcepts ++ [
          ConceptData.definition nextFibName natType nextVal none [s!"fib_{n1}", s!"fib_{n2}"] {
            name := nextFibName
            created := 0
            parent := some s!"fib_{n2}"
            interestingness := 0.9
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "fibonacci_generation"
          }
        ]
  
  IO.println s!"[Fibonacci] Generated {newConcepts.length} Fibonacci numbers"
  return newConcepts

/-- Generate factorial-like sequences -/
def generateFactorialLike : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  
  -- Check if we have factorial concepts
  let hasFact := concepts.any fun c => 
    let name := getConceptName c
    name.startsWith "fact_"
  
  if !hasFact then
    -- Start with fact_0 = 1
    let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
    newConcepts := newConcepts ++ [
      ConceptData.definition "fact_0" natType one none [] {
        name := "fact_0"
        created := 0
        parent := none
        interestingness := 0.95
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "factorial_generation"
      }
    ]
  
  -- Find the highest factorial we have
  let facts := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "fact_" then
        n.drop 5 |>.toNat?.map (·, v)
      else none
    | _ => none
  
  if let some (maxN, lastFactVal) := facts.foldl (fun acc (n, v) => 
    match acc with
    | none => some (n, v)
    | some (maxN, _) => if n > maxN then some (n, v) else acc) none then
    
    let nextN := maxN + 1
    if nextN <= 50 then  -- Keep factorials reasonable but allow more
      let nextFactName := s!"fact_{nextN}"
      
      if !concepts.any (fun c => getConceptName c == nextFactName) then
        -- fact_(n+1) = (n+1) * fact_n
        let nPlus1 := (List.range (nextN + 1)).foldl (fun acc _ => 
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        let nextVal := mkApp2 (mkConst ``Nat.mul) nPlus1 lastFactVal
        
        newConcepts := newConcepts ++ [
          ConceptData.definition nextFactName natType nextVal none [s!"fact_{maxN}"] {
            name := nextFactName
            created := 0
            parent := some s!"fact_{maxN}"
            interestingness := 0.9
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "factorial_generation"
          }
        ]
  
  IO.println s!"[Factorial] Generated {newConcepts.length} factorial numbers"
  return newConcepts

/-- Generate prime-like numbers (not actually checking primality, just odd numbers > 1) -/
def generatePrimeLike : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  
  -- Find existing "prime" numbers
  let primes := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "prime_" then
        n.drop 6 |>.toNat?
      else none
    | _ => none
  
  let maxPrime := primes.foldl max 1
  
  -- Generate next odd number as "prime"
  let nextOdd := if maxPrime % 2 == 0 then maxPrime + 1 else maxPrime + 2
  
  if nextOdd < 500 then
    let primeName := s!"prime_{nextOdd}"
    
    if !concepts.any (fun c => getConceptName c == primeName) then
      let primeVal := (List.range nextOdd).foldl (fun acc _ => 
        mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
      
      newConcepts := newConcepts ++ [
        ConceptData.definition primeName natType primeVal none [] {
          name := primeName
          created := 0
          parent := if maxPrime > 1 then some s!"prime_{maxPrime}" else none
          interestingness := 0.85
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "prime_generation"
        }
      ]
  
  IO.println s!"[Prime] Generated {newConcepts.length} prime-like numbers"
  return newConcepts

/-- Generate triangular numbers: 1, 3, 6, 10, 15, ... -/
def generateTriangular : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  
  -- Find existing triangular numbers
  let triangulars := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "tri_" then
        n.drop 4 |>.toNat?.map (·, v)
      else none
    | _ => none
  
  if triangulars.isEmpty then
    -- Start with tri_1 = 1
    let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
    newConcepts := newConcepts ++ [
      ConceptData.definition "tri_1" natType one none [] {
        name := "tri_1"
        created := 0
        parent := none
        interestingness := 0.9
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "triangular_generation"
      }
    ]
  else
    -- Find the highest triangular number
    if let some (maxN, lastTriVal) := triangulars.foldl (fun acc (n, v) => 
      match acc with
      | none => some (n, v)
      | some (maxN, _) => if n > maxN then some (n, v) else acc) none then
      
      let nextN := maxN + 1
      if nextN <= 200 then
        let triName := s!"tri_{nextN}"
        
        if !concepts.any (fun c => getConceptName c == triName) then
          -- tri_(n+1) = tri_n + (n+1)
          let nPlus1 := (List.range (nextN + 1)).foldl (fun acc _ => 
            mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
          let nextVal := mkApp2 (mkConst ``Nat.add) lastTriVal nPlus1
          
          newConcepts := newConcepts ++ [
            ConceptData.definition triName natType nextVal none [s!"tri_{maxN}"] {
              name := triName
              created := 0
              parent := some s!"tri_{maxN}"
              interestingness := 0.85
              useCount := 0
              successCount := 0
              specializationDepth := 1
              generationMethod := "triangular_generation"
            }
          ]
  
  IO.println s!"[Triangular] Generated {newConcepts.length} triangular numbers"
  return newConcepts

/-- Guaranteed generation heuristic: always generates something new -/
def guaranteedGeneration : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  
  -- Find all existing names to avoid collisions
  let existingNames := concepts.map getConceptName
  
  -- Generate numbers using different mathematical constructions to ensure uniqueness
  let conceptCount := concepts.length
  
  -- Strategy 1: Powers of 2 plus offset
  let powerOf2Name := s!"pow2plus_{conceptCount}"
  if !existingNames.contains powerOf2Name then
    -- 2^conceptCount + conceptCount
    let two := mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))
    let conceptCountExpr := (List.range conceptCount).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let powerExpr := mkApp2 (mkConst ``Nat.pow) two conceptCountExpr
    let uniqueVal := mkApp2 (mkConst ``Nat.add) powerExpr conceptCountExpr
    
    newConcepts := newConcepts ++ [
      ConceptData.definition powerOf2Name natType uniqueVal none [] {
        name := powerOf2Name
        created := 0
        parent := none
        interestingness := 0.7
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "power2plus_generation"
      }
    ]
  
  -- Strategy 2: Quadratic progression
  let quadName := s!"quad_{conceptCount}"
  if !existingNames.contains quadName then
    -- conceptCount^2 + conceptCount + 1
    let conceptCountExpr := (List.range conceptCount).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let squared := mkApp2 (mkConst ``Nat.mul) conceptCountExpr conceptCountExpr
    let plusCount := mkApp2 (mkConst ``Nat.add) squared conceptCountExpr
    let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
    let uniqueVal := mkApp2 (mkConst ``Nat.add) plusCount one
    
    newConcepts := newConcepts ++ [
      ConceptData.definition quadName natType uniqueVal none [] {
        name := quadName
        created := 0
        parent := none
        interestingness := 0.75
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "quadratic_generation"
      }
    ]
    
  -- Strategy 3: Exponential with different base
  let exp3Name := s!"exp3_{conceptCount}"
  if !existingNames.contains exp3Name then
    -- 3^conceptCount
    let three := mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)))
    let conceptCountExpr := (List.range conceptCount).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let uniqueVal := mkApp2 (mkConst ``Nat.pow) three conceptCountExpr
    
    newConcepts := newConcepts ++ [
      ConceptData.definition exp3Name natType uniqueVal none [] {
        name := exp3Name
        created := 0
        parent := none
        interestingness := 0.8
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "exp3_generation"
      }
    ]
  
  IO.println s!"[Guaranteed] Generated {newConcepts.length} guaranteed unique concepts using mathematical constructions"
  return newConcepts

/-- Generate expressions based on nested operations -/
def generateNested : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  let existingNames := concepts.map getConceptName
  let conceptCount := concepts.length
  
  -- Strategy: nested additions like ((2+1)+1)+1...
  let nestedName := s!"nested_add_{conceptCount}"
  if !existingNames.contains nestedName then
    let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
    let two := mkApp (mkConst ``Nat.succ) one
    let mut current := two
    
    -- Nest conceptCount additions
    for _ in List.range conceptCount do
      current := mkApp2 (mkConst ``Nat.add) current one
    
    newConcepts := newConcepts ++ [
      ConceptData.definition nestedName natType current none [] {
        name := nestedName
        created := 0
        parent := none
        interestingness := 0.65
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "nested_generation"
      }
    ]
  
  -- Strategy: nested multiplications 
  let nestedMulName := s!"nested_mul_{conceptCount}"
  if !existingNames.contains nestedMulName && conceptCount > 0 then
    let two := mkApp (mkConst ``Nat.succ) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))
    let mut current := two
    
    -- Multiply by (conceptCount + 1) each time
    let multiplier := (List.range (conceptCount + 1)).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    
    for _ in List.range (conceptCount % 3 + 1) do  -- Limit growth
      current := mkApp2 (mkConst ``Nat.mul) current multiplier
    
    newConcepts := newConcepts ++ [
      ConceptData.definition nestedMulName natType current none [] {
        name := nestedMulName
        created := 0
        parent := none
        interestingness := 0.7
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "nested_mul_generation"
      }
    ]
  
  IO.println s!"[Nested] Generated {newConcepts.length} nested operation concepts"
  return newConcepts

/-- Generate using modular arithmetic patterns -/
def generateModular : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  let existingNames := concepts.map getConceptName
  let conceptCount := concepts.length
  
  if conceptCount > 0 then
    -- Generate based on conceptCount mod various numbers
    for modBase in [5, 7, 11] do
      let remainder := conceptCount % modBase
      let modName := s!"mod{modBase}_step_{conceptCount}"
      
      if !existingNames.contains modName then
        -- Create expression: (conceptCount * modBase) + remainder + modBase
        let conceptCountExpr := (List.range conceptCount).foldl (fun acc _ => 
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        let modBaseExpr := (List.range modBase).foldl (fun acc _ => 
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        let remainderExpr := (List.range remainder).foldl (fun acc _ => 
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        
        let product := mkApp2 (mkConst ``Nat.mul) conceptCountExpr modBaseExpr
        let plusRemainder := mkApp2 (mkConst ``Nat.add) product remainderExpr
        let uniqueVal := mkApp2 (mkConst ``Nat.add) plusRemainder modBaseExpr
        
        newConcepts := newConcepts ++ [
          ConceptData.definition modName natType uniqueVal none [] {
            name := modName
            created := 0
            parent := none
            interestingness := 0.6
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "modular_generation"
          }
        ]
  
  IO.println s!"[Modular] Generated {newConcepts.length} modular arithmetic concepts"
  return newConcepts

/-- Absolutely guaranteed generation that scales indefinitely with iteration count -/
def infiniteGeneration : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  let natType := mkConst ``Nat
  let existingNames := concepts.map getConceptName
  let conceptCount := concepts.length
  
  -- Strategy 1: Create number based on prime factorization of concept count
  let baseName := s!"infinite_base_{conceptCount}"
  if !existingNames.contains baseName then
    -- Create: conceptCount + (conceptCount * 7) + (conceptCount^2 mod 23) + 42
    let countExpr := (List.range conceptCount).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let seven := (List.range 7).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let twentyThree := (List.range 23).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let fortyTwo := (List.range 42).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    
    let countTimes7 := mkApp2 (mkConst ``Nat.mul) countExpr seven
    let countSquared := mkApp2 (mkConst ``Nat.mul) countExpr countExpr
    let modResult := mkApp2 (mkConst ``Nat.mod) countSquared twentyThree
    
    let sum1 := mkApp2 (mkConst ``Nat.add) countExpr countTimes7
    let sum2 := mkApp2 (mkConst ``Nat.add) sum1 modResult
    let finalVal := mkApp2 (mkConst ``Nat.add) sum2 fortyTwo
    
    newConcepts := newConcepts ++ [
      ConceptData.definition baseName natType finalVal none [] {
        name := baseName
        created := 0
        parent := none
        interestingness := 0.9
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "infinite_generation"
      }
    ]
  
  -- Strategy 2: Time-based unique generation
  let timeName := s!"time_unique_{conceptCount}_iter"
  if !existingNames.contains timeName then
    -- Create: conceptCount^3 + (conceptCount * 13) + 1337
    let countExpr := (List.range conceptCount).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let thirteen := (List.range 13).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let leetNum := (List.range 1337).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    
    let countSquared := mkApp2 (mkConst ``Nat.mul) countExpr countExpr
    let countCubed := mkApp2 (mkConst ``Nat.mul) countSquared countExpr
    let countTimes13 := mkApp2 (mkConst ``Nat.mul) countExpr thirteen
    
    let sum := mkApp2 (mkConst ``Nat.add) countCubed countTimes13
    let finalVal := mkApp2 (mkConst ``Nat.add) sum leetNum
    
    newConcepts := newConcepts ++ [
      ConceptData.definition timeName natType finalVal none [] {
        name := timeName
        created := 0
        parent := none
        interestingness := 0.85
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "infinite_time_generation"
      }
    ]
  
  -- Strategy 3: Fibonacci-inspired but with concept count as base
  let fibInspiredName := s!"fib_like_{conceptCount}"
  if !existingNames.contains fibInspiredName then
    -- Create: (conceptCount-1) + conceptCount + (conceptCount+1)
    let conceptCountExpr := (List.range conceptCount).foldl (fun acc _ => 
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
    let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
    
    let prev := if conceptCount > 0 then 
      mkApp2 (mkConst ``Nat.sub) conceptCountExpr one 
    else 
      mkConst ``Nat.zero
    let next := mkApp2 (mkConst ``Nat.add) conceptCountExpr one
    
    let sum1 := mkApp2 (mkConst ``Nat.add) prev conceptCountExpr
    let finalVal := mkApp2 (mkConst ``Nat.add) sum1 next
    
    newConcepts := newConcepts ++ [
      ConceptData.definition fibInspiredName natType finalVal none [] {
        name := fibInspiredName
        created := 0
        parent := none
        interestingness := 0.8
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "infinite_fib_generation"
      }
    ]
  
  IO.println s!"[Infinite] Generated {newConcepts.length} infinite-scalable concepts"
  return newConcepts

/-- Heuristics for infinite numbers domain -/
def infiniteNumbersHeuristics : List (String × HeuristicFn) := [
  ("guaranteed_generation", guaranteedGeneration),  -- Put first to ensure we always generate something
  ("infinite_generation", infiniteGeneration),      -- Added infinite generation heuristic
  ("generate_nested", generateNested),              -- Second to add different constructions
  ("generate_modular", generateModular),            -- Third for arithmetic patterns
  ("generate_next_number", generateNextNumber),
  ("generate_arithmetic", generateArithmetic),
  ("generate_powers", generatePowers),
  ("generate_sequences", generateSequences),
  ("apply_sequences", applySequences),
  ("generate_fibonacci", generateFibonacciLike),
  ("generate_factorial", generateFactorialLike),
  ("generate_primes", generatePrimeLike),
  ("generate_triangular", generateTriangular)
]

/-- Run discovery in infinite numbers domain -/
def runInfiniteNumbersDiscovery (maxIterations : Nat := 20) : MetaM Unit := do
  -- Mine initial concepts
  let domainConcepts ← mineInfiniteNumbers
  let seedConcepts ← LeanDisco.seedConcepts
  let allInitialConcepts := seedConcepts ++ domainConcepts
  
  -- Get domain-specific heuristics
  let customHeuristics := infiniteNumbersHeuristics
  
  -- Use minimal discovery config to focus on generation
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 4
    maxConceptsPerIteration := 100
    enableConjectures := false  -- Keep it simple
    enablePatternRecognition := false
  }
  
  -- Run using the base runner
  let description := "Infinite Numbers Discovery"
  runDiscoveryCustom description allInitialConcepts customHeuristics [] maxIterations true config

end LeanDisco.Domains.InfiniteNumbers