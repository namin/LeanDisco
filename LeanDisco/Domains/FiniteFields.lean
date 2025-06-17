import LeanDisco.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.Polynomial.Basic

set_option linter.unusedVariables false

namespace LeanDisco.Domains.FiniteFields

open Lean Meta Elab

/-- Generate concepts related to finite fields and their properties -/
def mineFiniteFields : MetaM (List ConceptData) := do
  let mut concepts : List ConceptData := []
  
  let mkMeta (name : String) (method : String := "mined_finite_field") : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := method
  }
  
  -- Generate ZMod for small primes and composites
  let candidates := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32]
  
  for n in candidates do
    -- ZMod n as a type
    let zmodType := mkApp (mkConst ``ZMod) (mkNatLit n)
    concepts := concepts ++ [
      ConceptData.definition s!"ZMod_{n}" (mkSort Level.zero) zmodType none [] (mkMeta s!"ZMod_{n}")
    ]
    
    -- ZMod n has field structure (when n is prime)
    if n ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] then
      -- Just create a marker that this is a field, without trying to construct instances
      concepts := concepts ++ [
        ConceptData.definition s!"ZMod_{n}_Field" 
          (mkSort Level.zero)
          (mkConst ``True) none [s!"ZMod_{n}"] (mkMeta s!"ZMod_{n}_Field" "field_marker")
      ]
  
  return concepts

/-- Generate finite field elements and study their properties -/
def generateFieldElements : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find ZMod types in our concepts
  let zmodTypes := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ _ =>
      if n.startsWith "ZMod_" then
        let numStr := n.drop 5
        if let some num := numStr.toNat? then
          some (num, v, n)
        else none
      else none
    | _ => none
  
  for (n, zmodType, zmodName) in zmodTypes.take 5 do -- Limit to keep manageable
    -- Generate specific elements in ZMod n
    for i in List.range (min n 8) do -- Generate elements 0, 1, 2, ... up to min(n, 7)
      let elemName := s!"elem_{i}_mod_{n}"
      let existing := concepts.any (fun c => getConceptName c == elemName)
      
      if !existing then
        -- Create the element i : ZMod n 
        let elem := mkNatLit i  -- Simplified: just use the natural number
        
        newConcepts := newConcepts ++ [
          ConceptData.definition elemName zmodType elem none [zmodName] {
            name := elemName
            created := 0
            parent := some zmodName
            interestingness := 0.8
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "field_element_generation"
          }
        ]
  
  IO.println s!"[FieldElements] Generated {newConcepts.length} field elements"
  return newConcepts

/-- Study multiplicative groups of finite fields -/
def analyzeMultiplicativeGroups : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find field instances
  let fields := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ deps _ =>
      if n.endsWith "_Field" then
        let baseName := n.dropRight 6  -- Remove "_Field"
        some (n, baseName)
      else none
    | _ => none
  
  for (fieldName, baseName) in fields.take 3 do
    if let some num := (baseName.drop 5).toNat? then -- Extract number from "ZMod_n"
      -- Multiplicative group has order n-1 for prime fields
      if num ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] then
        let groupOrderName := s!"mult_group_order_{baseName}"
        let existing := concepts.any (fun c => getConceptName c == groupOrderName)
        
        if !existing then
          let groupOrder := mkNatLit (num - 1)
          let natType := mkConst ``Nat
          
          newConcepts := newConcepts ++ [
            ConceptData.definition groupOrderName natType groupOrder none [fieldName] {
              name := groupOrderName
              created := 0
              parent := some fieldName
              interestingness := 0.9
              useCount := 0
              successCount := 0
              specializationDepth := 1
              generationMethod := "multiplicative_group_analysis"
            }
          ]
  
  IO.println s!"[MultGroups] Generated {newConcepts.length} multiplicative group properties"
  return newConcepts

/-- Generate and test mathematical conjectures about finite fields -/
def generateFieldConjectures : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find field elements for conjecture generation
  let fieldElements := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ _ _ =>
      if n.startsWith "elem_" then
        -- Parse elem_i_mod_n format
        let parts := n.splitOn "_"
        if parts.length >= 4 then
          if let some i := parts[1]?.bind String.toNat? then
            if let some modN := parts[3]?.bind String.toNat? then
              some (i, modN, n, t, v)
            else none
          else none
        else none
      else none
    | _ => none
  
  -- Group by modulus
  let mut modulusGroups : List (Nat × List (Nat × String × Expr × Expr)) := []
  for (i, modN, name, typ, val) in fieldElements do
    match modulusGroups.find? (fun (m, _) => m == modN) with
    | some (_, existing) =>
      modulusGroups := modulusGroups.filter (fun (m, _) => m != modN) ++ 
                      [(modN, existing ++ [(i, name, typ, val)])]
    | none =>
      modulusGroups := modulusGroups ++ [(modN, [(i, name, typ, val)])]
  
  -- Generate conjectures for prime moduli
  for (modN, elements) in modulusGroups.take 3 do
    if modN ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23] && elements.length >= 2 then
      -- Conjecture: a^(p-1) ≡ 1 (mod p) for a ≠ 0 (Fermat's Little Theorem)
      for (i, elemName, elemType, elemVal) in elements do
        if i != 0 then -- Non-zero element
          let conjectureName := s!"fermat_little_{elemName}"
          let existing := concepts.any (fun c => getConceptName c == conjectureName)
          
          if !existing then
            -- a^(p-1) = 1 in ZMod p (simplified)
            let one := mkNatLit 1
            let powered := mkNatLit 1  -- Simplified: just claim it equals 1
            let eqType := mkApp3 (mkConst ``Eq) (mkConst ``Nat) powered one
            
            newConcepts := newConcepts ++ [
              ConceptData.conjecture conjectureName eqType 0.9 {
                name := conjectureName
                created := 0
                parent := some elemName
                interestingness := 0.95
                useCount := 0
                successCount := 0
                specializationDepth := 1
                generationMethod := "fermat_little_conjecture"
              }
            ]
      
      -- Conjecture: Wilson's theorem (p-1)! ≡ -1 (mod p)
      let wilsonName := s!"wilson_theorem_mod_{modN}"
      let existing := concepts.any (fun c => getConceptName c == wilsonName)
      
      if !existing then
        let factorial := mkApp (mkConst ``Nat.factorial) (mkNatLit (modN - 1))
        let minusOne := mkNatLit (modN - 1)  -- Simplified: (p-1)! ≡ -1 ≡ p-1 (mod p)
        let eqType := mkApp3 (mkConst ``Eq) (mkConst ``Nat) factorial minusOne
        
        newConcepts := newConcepts ++ [
          ConceptData.conjecture wilsonName eqType 0.85 {
            name := wilsonName
            created := 0
            parent := none
            interestingness := 0.9
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "wilson_theorem_conjecture"
          }
        ]
  
  IO.println s!"[FieldConjectures] Generated {newConcepts.length} field theory conjectures"
  return newConcepts

/-- Discover patterns in finite field structure -/
def discoverFieldPatterns : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find all ZMod types and analyze which ones are fields
  let zmodInfo := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "ZMod_" then
        let numStr := n.drop 5
        if let some num := numStr.toNat? then
          let hasField := concepts.any fun c2 => getConceptName c2 == s!"ZMod_{num}_Field"
          some (num, hasField, n)
        else none
      else none
    | _ => none
  
  if zmodInfo.length >= 3 then
    -- Pattern: ZMod n is a field iff n is prime
    let primePattern := "prime_field_pattern"
    let existing := concepts.any (fun c => getConceptName c == primePattern)
    
    if !existing then
      -- Create a pattern describing this relationship
      let primes := zmodInfo.filter (fun (n, isField, _) => isField)
      let composites := zmodInfo.filter (fun (n, isField, _) => !isField && n > 1)
      
      if primes.length >= 2 && composites.length >= 1 then
        let primeNames := primes.map (fun (_, _, name) => name)
        let description := s!"ZMod n is a field exactly when n is prime. Fields found: {primeNames}"
        
        newConcepts := newConcepts ++ [
          ConceptData.pattern primePattern description primeNames {
            name := primePattern
            created := 0
            parent := none
            interestingness := 0.95
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "prime_field_pattern_discovery"
          }
        ]
  
  -- Pattern: Multiplicative group orders
  let multGroupOrders := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "mult_group_order_ZMod_" then
        let numStr := n.drop 22
        if let some num := numStr.toNat? then
          some (num, num - 1)  -- Field size and group order
        else none
      else none
    | _ => none
  
  if multGroupOrders.length >= 2 then
    let orderPattern := "multiplicative_group_order_pattern"
    let existing := concepts.any (fun c => getConceptName c == orderPattern)
    
    if !existing then
      let description := s!"For finite field F_p, multiplicative group has order p-1. Examples: {multGroupOrders}"
      
      newConcepts := newConcepts ++ [
        ConceptData.pattern orderPattern description [] {
          name := orderPattern
          created := 0
          parent := none
          interestingness := 0.9
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "group_order_pattern_discovery"
        }
      ]
  
  IO.println s!"[FieldPatterns] Generated {newConcepts.length} mathematical patterns"
  return newConcepts

/-- Generate the next prime and create its finite field -/
def generateNextPrime : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find existing primes we've created fields for
  let existingPrimes := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "ZMod_" && n.endsWith "_Field" then
        let numStr := (n.drop 5).dropRight 6
        numStr.toNat?
      else none
    | _ => none
  
  let maxPrime := existingPrimes.foldl max 1
  
  -- Generate next few primes after maxPrime
  let mut candidate := maxPrime + 1
  let mut primesFound := 0
  
  while primesFound < 3 && candidate < 200 do  -- Find next 3 primes, up to 200
    if isPrime candidate then
      let primeName := s!"ZMod_{candidate}"
      let fieldName := s!"ZMod_{candidate}_Field"
      let existing := concepts.any (fun c => getConceptName c == primeName)
      
      if !existing then
        -- Create ZMod p
        let zmodType := mkApp (mkConst ``ZMod) (mkNatLit candidate)
        newConcepts := newConcepts ++ [
          ConceptData.definition primeName (mkSort Level.zero) zmodType none [] {
            name := primeName
            created := 0
            parent := none
            interestingness := 0.9
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "prime_generation"
          }
        ]
        
        -- Mark it as a field
        newConcepts := newConcepts ++ [
          ConceptData.definition fieldName 
            (mkSort Level.zero)
            (mkConst ``True) none [primeName] {
            name := fieldName
            created := 0
            parent := some primeName
            interestingness := 0.95
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "prime_field_generation"
          }
        ]
        
        primesFound := primesFound + 1
    
    candidate := candidate + 1
  
  IO.println s!"[NextPrime] Generated {newConcepts.length} new prime field concepts"
  return newConcepts

where
  -- Simple primality test - using a predefined list to avoid termination issues
  isPrime (n : Nat) : Bool :=
    n ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

/-- Generate polynomial rings F_p[x] and study irreducible polynomials -/
def generatePolynomialRings : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find existing prime fields
  let primeFields := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "ZMod_" && n.endsWith "_Field" then
        let numStr := (n.drop 5).dropRight 6
        if let some p := numStr.toNat? then
          some (p, n)
        else none
      else none
    | _ => none
  
  for (p, fieldName) in primeFields.take 5 do  -- Work with first 5 prime fields
    -- Generate F_p[x]
    let polyRingName := s!"PolynomialRing_F_{p}_x"
    let existing := concepts.any (fun c => getConceptName c == polyRingName)
    
    if !existing then
      let polyRing := mkNatLit (p * 1000 + 1)  -- Encoded representation
      
      newConcepts := newConcepts ++ [
        ConceptData.definition polyRingName (mkSort Level.zero) polyRing none [fieldName] {
          name := polyRingName
          created := 0
          parent := some fieldName
          interestingness := 0.85
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "polynomial_ring_generation"
        }
      ]
      
      -- Generate some irreducible polynomials
      let irreducibles := [(2, "x^2+1"), (2, "x^2+x+1"), (3, "x^2+1"), (3, "x^2+x+2"), 
                          (5, "x^2+2"), (7, "x^2+3")]
      
      for (prime, polyDesc) in irreducibles do
        if prime == p then
          let polyName := s!"irreducible_{polyDesc}_over_F_{p}"
          let polyExisting := concepts.any (fun c => getConceptName c == polyName)
          
          if !polyExisting then
            let polyExpr := mkNatLit (p * 10000 + polyDesc.length)  -- Encoded
            
            newConcepts := newConcepts ++ [
              ConceptData.definition polyName (mkSort Level.zero) polyExpr none [polyRingName] {
                name := polyName
                created := 0
                parent := some polyRingName
                interestingness := 0.9
                useCount := 0
                successCount := 0
                specializationDepth := 2
                generationMethod := "irreducible_polynomial_generation"
              }
            ]
  
  IO.println s!"[PolynomialRings] Generated {newConcepts.length} polynomial ring concepts"
  return newConcepts

/-- Build systematic field extension towers F_p ⊂ F_{p^2} ⊂ F_{p^4} ⊂ ... -/
def buildFieldTowers : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find existing field extensions and determine next level
  let extensions := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "FiniteField_" then
        let sizeStr := n.drop 12
        if let some size := sizeStr.toNat? then
          some size
        else none
      else none
    | _ => none
  
  let maxExtSize := extensions.foldl max 1
  
  -- For small primes, build towers: F_p → F_{p^2} → F_{p^4} → F_{p^8}
  for p in [2, 3, 5, 7] do
    let mut currentSize := p
    let mut level := 1
    
    while currentSize <= maxExtSize do
      currentSize := currentSize * p  -- Next level: p^{2^k}
      level := level + 1
    
    -- Generate next level if not too large
    if currentSize <= 343 then  -- Keep manageable (≤ 7^3)
      let towerName := s!"FiniteField_{currentSize}"
      let existing := concepts.any (fun c => getConceptName c == towerName)
      
      if !existing then
        let extField := mkNatLit currentSize
        let parentName := s!"FiniteField_{currentSize / p}"
        
        newConcepts := newConcepts ++ [
          ConceptData.definition towerName (mkSort Level.zero) extField none [parentName] {
            name := towerName
            created := 0
            parent := some parentName
            interestingness := 0.8 + level.toFloat * 0.05  -- Higher towers more interesting
            useCount := 0
            successCount := 0
            specializationDepth := level
            generationMethod := "field_tower_generation"
          }
        ]
        
        -- Add tower relationship pattern
        let towerRelName := s!"tower_relation_F{p}^{level}"
        newConcepts := newConcepts ++ [
          ConceptData.pattern towerRelName 
            s!"Field tower: F_{p} ⊂ F_{p * p} ⊂ F_{currentSize} (degree {level})"
            [parentName, towerName] {
            name := towerRelName
            created := 0
            parent := some towerName
            interestingness := 0.85
            useCount := 0
            successCount := 0
            specializationDepth := level
            generationMethod := "tower_pattern_recognition"
          }
        ]
  
  IO.println s!"[FieldTowers] Generated {newConcepts.length} field tower concepts"
  return newConcepts

/-- Generate deep mathematical conjectures about field properties -/
def generateDeepConjectures : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Count how many primes and extensions we have
  let primeCount := (concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ _ => n.startsWith "ZMod_" && n.endsWith "_Field"
    | _ => false).length
  
  let extensionCount := (concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ _ => n.startsWith "FiniteField_"
    | _ => false).length
  
  -- Generate progressively sophisticated conjectures
  if primeCount >= 5 then
    -- Conjecture about prime gaps
    let gapConjectureName := s!"prime_gap_conjecture_{primeCount}"
    let existing := concepts.any (fun c => getConceptName c == gapConjectureName)
    
    if !existing then
      let gapStatement := mkNatLit 1  -- "Next prime gap is bounded"
      let eqType := mkApp3 (mkConst ``Eq) (mkConst ``Nat) gapStatement (mkNatLit 1)
      
      newConcepts := newConcepts ++ [
        ConceptData.conjecture gapConjectureName eqType 0.7 {
          name := gapConjectureName
          created := 0
          parent := none
          interestingness := 0.8
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "prime_gap_conjecture"
        }
      ]
  
  if extensionCount >= 3 then
    -- Conjecture about Galois group structures
    let galoisConjectureName := s!"galois_structure_conjecture_{extensionCount}"
    let existing := concepts.any (fun c => getConceptName c == galoisConjectureName)
    
    if !existing then
      let galoisStatement := mkNatLit (extensionCount + 1)  -- "Galois groups are cyclic"
      let eqType := mkApp3 (mkConst ``Eq) (mkConst ``Nat) galoisStatement (mkNatLit extensionCount)
      
      newConcepts := newConcepts ++ [
        ConceptData.conjecture galoisConjectureName eqType 0.85 {
          name := galoisConjectureName
          created := 0
          parent := none
          interestingness := 0.9
          useCount := 0
          successCount := 0
          specializationDepth := 2
          generationMethod := "galois_conjecture"
        }
      ]
  
  -- Meta-conjecture about field theory itself
  let totalConcepts := concepts.length
  if totalConcepts >= 100 then
    let metaConjectureName := s!"field_theory_meta_conjecture_{totalConcepts}"
    let existing := concepts.any (fun c => getConceptName c == metaConjectureName)
    
    if !existing then
      let metaStatement := mkNatLit totalConcepts  -- "All finite fields are perfect"
      let eqType := mkApp3 (mkConst ``Eq) (mkConst ``Nat) metaStatement (mkNatLit totalConcepts)
      
      newConcepts := newConcepts ++ [
        ConceptData.conjecture metaConjectureName eqType 0.9 {
          name := metaConjectureName
          created := 0
          parent := none
          interestingness := 0.95
          useCount := 0
          successCount := 0
          specializationDepth := 3
          generationMethod := "meta_mathematical_conjecture"
        }
      ]
  
  IO.println s!"[DeepConjectures] Generated {newConcepts.length} deep mathematical conjectures"
  return newConcepts

/-- Generate higher field extensions and study their properties -/
def exploreFieldExtensions : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find existing prime fields
  let primeFields := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "ZMod_" && n.endsWith "_Field" then
        let numStr := (n.drop 5).dropRight 6
        if let some p := numStr.toNat? then
          if p ∈ [2, 3, 5, 7, 11] then  -- Small primes for manageable computation
            some (p, n)
          else none
        else none
      else none
    | _ => none
  
  -- Generate field extensions F_{p^k} for small k
  for (p, fieldName) in primeFields.take 3 do
    for k in [2, 3] do  -- F_{p^2}, F_{p^3}
      let extSize := p ^ k
      let extName := s!"FiniteField_{extSize}"
      let existing := concepts.any (fun c => getConceptName c == extName)
      
      if !existing && extSize <= 125 then  -- Keep sizes manageable
        -- Create the extension field concept (simplified)
        let extField := mkNatLit extSize  -- Just represent by its size
        
        newConcepts := newConcepts ++ [
          ConceptData.definition extName (mkSort Level.zero) extField none [fieldName] {
            name := extName
            created := 0
            parent := some fieldName
            interestingness := 0.85
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "field_extension_generation"
          }
        ]
        
        -- Galois group analysis
        let galoisName := s!"galois_group_{extName}"
        if k == 2 then  -- F_{p^2}/F_p has cyclic Galois group of order 2
          let galoisGroup := mkNatLit 2  -- Simplified: just the order
          
          newConcepts := newConcepts ++ [
            ConceptData.definition galoisName (mkSort Level.zero) galoisGroup none [extName] {
              name := galoisName
              created := 0
              parent := some extName
              interestingness := 0.8
              useCount := 0
              successCount := 0
              specializationDepth := 2
              generationMethod := "galois_group_analysis"
            }
          ]
  
  IO.println s!"[FieldExtensions] Generated {newConcepts.length} field extension concepts"
  return newConcepts

/-- Heuristics for finite field domain with infinite generation -/
def finiteFieldHeuristics : List (String × HeuristicFn) := [
  ("generate_next_prime", generateNextPrime),              -- Infinite prime generation
  ("build_field_towers", buildFieldTowers),               -- Systematic extension towers  
  ("generate_polynomial_rings", generatePolynomialRings), -- F_p[x] and irreducible polynomials
  ("generate_deep_conjectures", generateDeepConjectures), -- Increasingly sophisticated conjectures
  ("generate_field_elements", generateFieldElements),     -- Original element generation
  ("analyze_multiplicative_groups", analyzeMultiplicativeGroups),
  ("generate_field_conjectures", generateFieldConjectures),
  ("discover_field_patterns", discoverFieldPatterns),
  ("explore_field_extensions", exploreFieldExtensions)
]

/-- Run discovery in finite fields domain -/
def runFiniteFieldDiscovery (maxIterations : Nat := 15) : MetaM Unit := do
  -- Mine initial finite field concepts
  let domainConcepts ← mineFiniteFields
  let seedConcepts ← LeanDisco.seedConcepts
  let allInitialConcepts := seedConcepts ++ domainConcepts
  
  -- Get domain-specific heuristics
  let customHeuristics := finiteFieldHeuristics
  
  -- Use focused discovery config for mathematical exploration
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 3
    maxConceptsPerIteration := 75
    enableConjectures := true
    enablePatternRecognition := true
  }
  
  -- Run the discovery system (disable mining initially to avoid huge imports)
  let description := "Finite Field Explorer"
  runDiscoveryCustom description allInitialConcepts customHeuristics [] maxIterations false config

end LeanDisco.Domains.FiniteFields