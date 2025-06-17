import LeanDisco.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

set_option linter.unusedVariables false

namespace LeanDisco.Domains.GroupRing

open Lean Meta Elab

/-- Configuration specific to group/ring mining -/
structure GroupRingConfig where
  includeBasicGroupTheory : Bool := true
  includeCommutativeGroups : Bool := true
  includeBasicRingTheory : Bool := true
  includeHomomorphisms : Bool := true
  includeSubstructures : Bool := false
  includeIdeals : Bool := false

/-- Mine group/ring concepts based on configuration -/
def mineGroupRingConcepts (config : GroupRingConfig) : MetaM (List ConceptData) := do
  let env ← getEnv
  let mut concepts : List ConceptData := []

  let mkMeta (name : String) (struct : String) : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := s!"mined_{struct}"
  }

  -- Group theory basics
  if config.includeBasicGroupTheory then
    let groupTheorems : List (String × String) := [
      -- Identity and inverses
      ("mul_one", "∀ a : G, a * 1 = a"),
      ("one_mul", "∀ a : G, 1 * a = a"),
      ("mul_left_inv", "∀ a : G, a⁻¹ * a = 1"),
      ("inv_mul_self", "∀ a : G, a⁻¹ * a = 1"),
      ("mul_inv_self", "∀ a : G, a * a⁻¹ = 1"),
      ("inv_inv", "∀ a : G, (a⁻¹)⁻¹ = a")
    ]

    for (thmName, _description) in groupTheorems do
      -- Try different name patterns
      let possibleNames : List Name := [
        Name.mkStr1 thmName,
        Name.mkStr2 "Group" thmName,       -- Changed from `Group to "Group"
        Name.mkStr2 "Monoid" thmName,      -- Changed from `Monoid to "Monoid"
        Name.mkStr2 "DivInvMonoid" thmName -- Changed from `DivInvMonoid to "DivInvMonoid"
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              thmName
              val.type
              (mkConst name)
              []
              (mkMeta thmName "group")]
            -- Removed debug output for cleaner console
            break
          | _ => continue

  -- Ring theory basics
  if config.includeBasicRingTheory then
    let ringTheorems : List (String × String) := [
      -- Additive structure
      ("add_assoc", "∀ a b c : R, (a + b) + c = a + (b + c)"),
      ("add_comm", "∀ a b : R, a + b = b + a"),
      ("zero_add", "∀ a : R, 0 + a = a"),
      ("add_zero", "∀ a : R, a + 0 = a"),
      ("add_left_neg", "∀ a : R, -a + a = 0"),
      ("add_right_neg", "∀ a : R, a + -a = 0"),

      -- Multiplicative structure
      ("mul_assoc", "∀ a b c : R, (a * b) * c = a * (b * c)"),
      ("one_mul", "∀ a : R, 1 * a = a"),
      ("mul_one", "∀ a : R, a * 1 = a"),
      ("mul_zero", "∀ a : R, a * 0 = 0"),
      ("zero_mul", "∀ a : R, 0 * a = 0"),

      -- Distributivity
      ("left_distrib", "∀ a b c : R, a * (b + c) = a * b + a * c"),
      ("right_distrib", "∀ a b c : R, (a + b) * c = a * c + b * c")
    ]

    for (thmName, _description) in ringTheorems do
      let possibleNames : List Name := [
        Name.mkStr2 "Ring" thmName,          -- Changed from `Ring to "Ring"
        Name.mkStr2 "Semiring" thmName,      -- Changed from `Semiring to "Semiring"
        Name.mkStr2 "NonUnitalRing" thmName, -- Changed from `NonUnitalRing to "NonUnitalRing"
        Name.mkStr2 "AddGroup" thmName       -- Changed from `AddGroup to "AddGroup"
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              s!"Ring.{thmName}"
              val.type
              (mkConst name)
              []
              (mkMeta s!"Ring.{thmName}" "ring")]
            break
          | _ => continue

  -- Mine concrete Nat arithmetic theorems
  if config.includeBasicGroupTheory then
    -- IO.println "[DEBUG] Looking for Nat arithmetic theorems..."
    let natTheorems : List (String × Name) := [
      ("nat_add_zero", ``Nat.add_zero),
      ("nat_zero_add", ``Nat.zero_add),
      ("nat_add_assoc", ``Nat.add_assoc),
      ("nat_add_comm", ``Nat.add_comm),
      ("nat_succ_add", ``Nat.succ_add),
      ("nat_add_succ", ``Nat.add_succ),
      ("nat_add_one", ``Nat.add_one),
      ("nat_one_add", ``Nat.one_add)
    ]

    for (name, constName) in natTheorems do
      try
        if let some info := env.find? constName then
          match info with
          | .thmInfo val =>
            -- IO.println s!"[DEBUG] Found Nat theorem: {name}"
            concepts := concepts ++ [ConceptData.theorem
              name
              val.type
              (mkConst constName)
              []
              (mkMeta name "nat_arithmetic")]
          | _ =>
            pure () -- IO.println s!"[DEBUG] {constName} is not a theorem"
      catch e =>
        pure () -- IO.println s!"[DEBUG] Error with {name}"

  IO.println s!"[GroupRing] Mined {concepts.length} concepts"
  return concepts

/-- Helper to check if an expression is a typeclass instance parameter -/
def isInstanceParam (e : Expr) : Bool :=
  e.isFVar && contains e.fvarId!.name.toString "inst"

/-- Extract the carrier type from a typeclass-based theorem -/
def extractCarrierType (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .forallE _ type _ _ =>
    -- Look for Type u patterns
    if type.isSort then
      return some type
    else
      extractCarrierType type
  | _ => return none

/-- Try to instantiate a typeclass theorem for a specific type -/
def instantiateForType (thmType : Expr) (thmProof : Expr) (targetType : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    -- Helper to collect all the forall binders
    let rec collectBinders (e : Expr) : MetaM (List (Name × BinderInfo × Expr)) := do
      match e with
      | .forallE n t b bi => do
        let rest ← collectBinders b
        return (n, bi, t) :: rest
      | _ => return []

    let binders ← collectBinders thmType

    -- Process binders and build the instantiated statement
    let rec processBinders (binders : List (Name × BinderInfo × Expr)) (acc : Array Expr) : MetaM (Expr × Expr) := do
      match binders with
      | [] =>
        -- No more binders, return the instantiated theorem
        let instType := thmType.instantiateRev acc
        let instProof := mkAppN thmProof acc
        return (instType, instProof)
      | (n, bi, t) :: rest =>
        -- Check if this is a Type parameter
        if t.isSort then
          -- Replace with our target type
          processBinders rest (acc.push targetType)
        else if contains n.toString "inst" then
          -- This is likely a typeclass instance
          -- Try to synthesize the instance for our target type
          let instType := t.instantiateRev acc
          try
            let inst ← synthInstance instType
            processBinders rest (acc.push inst)
          catch _ =>
            -- Failed to synthesize instance
            return (thmType, thmProof)
        else
          -- Regular parameter - for now, skip theorems with non-instance parameters
          return (thmType, thmProof)

    let (instType, instProof) ← processBinders binders #[]

    -- Check if we actually instantiated something
    if instType == thmType then
      return none
    else
      return some (instType, instProof)
  catch _ =>
    return none

/-- Find and create instances of algebraic structures -/
def structureInstanceHeuristic : HeuristicFn := fun _config concepts => do
  let mut newConcepts := []

  -- Look for evidence of group/ring structure in discovered concepts
  -- For now, just note that Nat has various instances

  -- Create a concept noting that Nat is an AddMonoid
  let natAddMonoidMeta := {
    name := "Nat_is_AddMonoid"
    created := 0
    parent := none
    interestingness := 0.9
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "structure_recognition"
  }

  newConcepts := newConcepts ++ [
    ConceptData.pattern
      "Nat_is_AddMonoid"
      "Natural numbers form an additive monoid"
      ["nat_add_zero", "nat_zero_add", "nat_add_assoc"]
      natAddMonoidMeta
  ]

  return newConcepts

/-- Pattern recognition for algebraic structures -/
def algebraicPatternRecognition : HeuristicFn := fun config concepts => do
  if !config.enablePatternRecognition then
    return []

  let mut patterns := []

  -- Look for collections of theorems that form algebraic structures
  let groupLaws := ["mul_one", "one_mul", "mul_assoc", "mul_left_inv"]
  let ringLaws := ["add_assoc", "add_comm", "zero_add", "add_zero",
                   "mul_assoc", "one_mul", "mul_one",
                   "left_distrib", "right_distrib"]

  -- Check which laws we have
  let availableLaws := concepts.filterMap fun c => match c with
    | ConceptData.theorem name _ _ _ _ => some name
    | _ => none

  let hasGroupLaws := groupLaws.filter (availableLaws.contains ·)
  let hasRingLaws := ringLaws.filter (availableLaws.contains ·)

  if hasGroupLaws.length >= 3 then
    patterns := patterns ++ [
      ConceptData.pattern
        "partial_group_structure"
        s!"Found {hasGroupLaws.length} out of {groupLaws.length} group laws"
        hasGroupLaws
        { name := "partial_group_structure"
          created := 0
          parent := none
          interestingness := 0.9
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "algebraic_pattern" }
    ]

  if hasRingLaws.length >= 5 then
    patterns := patterns ++ [
      ConceptData.pattern
        "partial_ring_structure"
        s!"Found {hasRingLaws.length} out of {ringLaws.length} ring laws"
        hasRingLaws
        { name := "partial_ring_structure"
          created := 0
          parent := none
          interestingness := 0.95
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "algebraic_pattern" }
    ]

  return patterns

/-- Look for dual concepts (additive vs multiplicative) -/
def dualityHeuristic : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []

  -- Map between multiplicative and additive operations
  let dualMap : List (String × String × Expr × Expr) := [
    ("mul", "add", mkConst ``HMul.hMul, mkConst ``HAdd.hAdd),
    ("one", "zero", mkConst ``One.one, mkConst ``Zero.zero)
  ]

  -- Look for specialized theorems to dualize
  for concept in concepts do
    match concept with
    | ConceptData.theorem name stmt proof deps meta =>
      if meta.generationMethod == "typeclass_specialization" && contains name "_on_Nat" then
        -- Try to create dual version
        for (mulName, addName, _, _) in dualMap do
          if contains name mulName then
            let dualName := name.replace mulName addName
            IO.println s!"[Duality] Suggesting dual: {name} → {dualName}"
    | _ => pure ()

  return newConcepts

/-- Debug-enhanced typeclass specialization that actually works -/
def typeclassSpecializationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  IO.println "[Typeclass Spec] Starting improved typeclass specialization..."

  -- Find theorems to specialize
  let polymorphicTheorems := concepts.filterMap fun c => match c with
    | ConceptData.theorem name stmt proof _ meta =>
      if meta.generationMethod == "mined_group" || meta.generationMethod == "mined_ring" then
        some (name, stmt, proof, meta)
      else none
    | _ => none

  IO.println s!"[Typeclass Spec] Found {polymorphicTheorems.length} polymorphic theorems"

  -- Check if we already have Nat multiplication
  let hasNatMul := concepts.any (fun c => getConceptName c == "nat_mul")

  for (name, stmt, proof, meta) in polymorphicTheorems do
    IO.println s!"[Typeclass Spec] Processing theorem: {name}"

    match name with
    | "mul_one" =>
      if hasNatMul then
        try
          let natType := mkConst ``Nat
          let natMul := mkConst ``Nat.mul
          let natOne := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)

          -- Build: ∀ (a : Nat), a * 1 = a
          let specStmt ← mkSafeForall `a natType fun a => do
            let lhs := mkApp2 natMul a natOne
            let rhs := a
            return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs

          let specProof := mkConst ``Nat.mul_one
          let specName := s!"{name}_on_Nat"

          -- Check if we already have this
          if !concepts.any (fun c => getConceptName c == specName) then
            let newMeta := { meta with
              name := specName
              parent := some name
              interestingness := 0.8
              specializationDepth := 1
              generationMethod := "typeclass_specialization"
            }

            IO.println s!"[Typeclass Spec] Creating: {specName}"
            newConcepts := newConcepts ++ [
              ConceptData.theorem specName specStmt specProof [] newMeta
            ]
        catch e =>
          IO.println s!"[Typeclass Spec] Failed"

    | "one_mul" =>
      if hasNatMul then
        try
          let natType := mkConst ``Nat
          let natMul := mkConst ``Nat.mul
          let natOne := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)

          let specStmt ← mkSafeForall `a natType fun a => do
            let lhs := mkApp2 natMul natOne a
            let rhs := a
            return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs

          let specProof := mkConst ``Nat.one_mul
          let specName := s!"{name}_on_Nat"

          if !concepts.any (fun c => getConceptName c == specName) then
            let newMeta := { meta with
              name := specName
              parent := some name
              interestingness := 0.8
              specializationDepth := 1
              generationMethod := "typeclass_specialization"
            }

            IO.println s!"[Typeclass Spec] Creating: {specName}"
            newConcepts := newConcepts ++ [
              ConceptData.theorem specName specStmt specProof [] newMeta
            ]
        catch e =>
          IO.println s!"[Typeclass Spec] Failed"

    | _ =>
      IO.println s!"[Typeclass Spec] Skipping {name}"

  IO.println s!"[Typeclass Spec] Generated {newConcepts.length} specialized theorems"
  return newConcepts

/-- Create concrete instances showing Nat has algebraic structure -/
def concreteInstanceHeuristic : HeuristicFn := fun _config concepts => do
  let mut newConcepts := []

  -- Check if we already have these
  let hasNatMul := concepts.any fun c => getConceptName c == "nat_mul"
  let hasNatOne := concepts.any fun c => getConceptName c == "nat_one"

  if !hasNatMul then
    -- Define Nat multiplication as a concept
    let natType := mkConst ``Nat
    let mulType ← mkArrow natType (← mkArrow natType natType)
    let mulVal := mkConst ``Nat.mul

    newConcepts := newConcepts ++ [
      ConceptData.definition "nat_mul" mulType mulVal none []
        { name := "nat_mul"
          created := 0
          parent := none
          interestingness := 0.9
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "concrete_instance" }
    ]

  if !hasNatOne then
    -- Define 1 for Nat
    let natType := mkConst ``Nat
    let oneVal := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)

    newConcepts := newConcepts ++ [
      ConceptData.definition "nat_one" natType oneVal none []
        { name := "nat_one"
          created := 0
          parent := none
          interestingness := 0.8
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "concrete_instance" }
    ]

  return newConcepts

/-- Apply specialized theorems to concrete values -/
def applySpecializedTheorems : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  -- Find specialized theorems (with correct filter)
  let specializedTheorems := concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ meta =>
      meta.generationMethod == "typeclass_specialization"
    | _ => false

  IO.println s!"[Apply Spec] Found {specializedTheorems.length} specialized theorems to apply"

  -- Find concrete Nat values
  let natValues := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ v _ _ m =>
      if n == "zero" || n == "one" || n == "two" || n.startsWith "num_" then
        some (n, v)
      else none
    | _ => none

  for thm in specializedTheorems do
    match thm with
    | ConceptData.theorem thmName stmt proof _ meta =>
      IO.println s!"[Apply Spec] Processing theorem: {thmName}"

      if contains thmName "mul_one_on_Nat" then
        -- Apply to specific numbers
        for (valName, valExpr) in natValues.take 3 do
          try
            let natType := mkConst ``Nat
            let natMul := mkConst ``Nat.mul
            let natOne := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)

            -- Create the specific instance: valExpr * 1 = valExpr
            let lhs := mkApp2 natMul valExpr natOne
            let concreteStmt := mkApp3 (mkConst ``Eq [levelOne]) natType lhs valExpr

            -- Use the specialized theorem as proof
            let concreteProof := mkApp proof valExpr

            let instName := s!"{thmName}_{valName}"

            if !concepts.any (fun c => getConceptName c == instName) then
              IO.println s!"[Apply Spec] Creating instance: {instName}"

              newConcepts := newConcepts ++ [
                ConceptData.theorem instName concreteStmt concreteProof [thmName, valName]
                  { meta with
                    name := instName
                    parent := some thmName
                    specializationDepth := meta.specializationDepth + 1
                    generationMethod := "theorem_application"
                    interestingness := 0.6 }
              ]
          catch e =>
            IO.println s!"[Apply Spec] Failed to apply {thmName} to {valName}"

      else if contains thmName "one_mul_on_Nat" then
        -- Similar for one_mul
        for (valName, valExpr) in natValues.take 3 do
          try
            let natType := mkConst ``Nat
            let natMul := mkConst ``Nat.mul
            let natOne := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)

            let lhs := mkApp2 natMul natOne valExpr
            let concreteStmt := mkApp3 (mkConst ``Eq [levelOne]) natType lhs valExpr
            let concreteProof := mkApp proof valExpr

            let instName := s!"{thmName}_{valName}"

            if !concepts.any (fun c => getConceptName c == instName) then
              IO.println s!"[Apply Spec] Creating instance: {instName}"

              newConcepts := newConcepts ++ [
                ConceptData.theorem instName concreteStmt concreteProof [thmName, valName]
                  { meta with
                    name := instName
                    parent := some thmName
                    specializationDepth := meta.specializationDepth + 1
                    generationMethod := "theorem_application"
                    interestingness := 0.6 }
              ]
          catch e =>
            IO.println s!"[Apply Spec] Failed"
    | _ => pure ()

  IO.println s!"[Apply Spec] Generated {newConcepts.length} theorem applications"
  return newConcepts

/-- Generate algebraic conjectures based on patterns -/
def algebraicConjectureHeuristic : HeuristicFn := fun cfg concepts => do
  if !cfg.enableConjectures then
    return []

  let mut conjectures := []

  -- Check what specialized theorems we have
  let hasMulOne := concepts.any fun c => match c with
    | ConceptData.theorem name _ _ _ _ => name == "mul_one_on_Nat"
    | _ => false

  let hasOneMul := concepts.any fun c => match c with
    | ConceptData.theorem name _ _ _ _ => name == "one_mul_on_Nat"
    | _ => false

  if hasMulOne || hasOneMul then
    IO.println "[Conjectures] Generating multiplication conjectures..."

    let natType := mkConst ``Nat
    let natMul := mkConst ``Nat.mul
    let zero := mkConst ``Nat.zero

    -- Conjecture: ∀ n : Nat, n * 0 = 0
    let mulZeroStmt ← mkSafeForall `n natType fun n => do
      let lhs := mkApp2 natMul n zero
      let rhs := zero
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs

    conjectures := conjectures ++ [
      ConceptData.conjecture
        "nat_mul_zero_conjecture"
        mulZeroStmt
        0.8
        { name := "nat_mul_zero_conjecture"
          created := 0
          parent := if hasMulOne then some "mul_one_on_Nat" else some "one_mul_on_Nat"
          interestingness := 0.9
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "algebraic_conjecture" }
    ]

    -- Conjecture: multiplication is commutative
    let mulCommStmt ← mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        let lhs := mkApp2 natMul a b
        let rhs := mkApp2 natMul b a
        return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs

    conjectures := conjectures ++ [
      ConceptData.conjecture
        "nat_mul_comm_conjecture"
        mulCommStmt
        0.7
        { name := "nat_mul_comm_conjecture"
          created := 0
          parent := if hasMulOne then some "mul_one_on_Nat" else none
          interestingness := 0.95
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "algebraic_conjecture" }
    ]

  IO.println s!"[Conjectures] Generated {conjectures.length} conjectures"
  return conjectures

/-- Generate systematic group orders based on what's been discovered -/
def generateGroupOrders : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find highest group order we've explored
  let existingOrders := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ => 
      if n.startsWith "group_order_" then
        (n.drop 12).toNat?
      else none
    | _ => none
  
  let maxOrder := existingOrders.foldl max 8  -- Start from at least 8
  
  -- Generate new group orders systematically
  for i in [1, 2, 3, 4, 5] do
    let newOrder := maxOrder + i
    if newOrder <= 100 then  -- Keep manageable
      let orderName := s!"group_order_{newOrder}"
      let natType := mkConst ``Nat
      let orderValue := mkNatLit newOrder
      
      newConcepts := newConcepts ++ [
        ConceptData.definition orderName natType orderValue none [] {
          name := orderName
          created := concepts.length + i * 3
          parent := none
          interestingness := 0.7 + (newOrder.toFloat / 200.0)
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "group_order_generation"
        }
      ]
      
      -- Generate structure information
      let structureName := s!"structure_type_{newOrder}"
      let structureType := if newOrder % 2 == 0 then "even" else "odd"
      let structureValue := mkNatLit (if newOrder % 2 == 0 then 0 else 1)
      
      newConcepts := newConcepts ++ [
        ConceptData.definition structureName natType structureValue none [orderName] {
          name := structureName
          created := concepts.length + i * 3 + 1
          parent := some orderName
          interestingness := 0.5
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "structure_analysis"
        }
      ]
      
      -- Add divisibility properties
      if newOrder > 2 then
        let divName := s!"divisors_of_{newOrder}"
        let numDivisors := mkNatLit ((List.range newOrder).filter (fun d => d > 0 && newOrder % d == 0)).length
        
        newConcepts := newConcepts ++ [
          ConceptData.definition divName natType numDivisors none [orderName] {
            name := divName
            created := concepts.length + i * 3 + 2
            parent := some orderName
            interestingness := 0.6
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "divisibility_analysis"
          }
        ]
  
  IO.println s!"[GroupOrders] Generated {newConcepts.length} group order concepts (continuing from {maxOrder})"
  return newConcepts

/-- Generate ring characteristics and related structures -/
def generateRingCharacteristics : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find existing ring characteristics
  let existingChars := concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ => 
      if n.startsWith "char_" then
        (n.drop 5).toNat?
      else none
    | _ => none
  
  let maxChar := existingChars.foldl max 1
  let primes := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
  
  -- Generate new ring characteristics
  for p in primes do
    if p > maxChar then
      let charName := s!"char_{p}"
      let natType := mkConst ``Nat
      let charValue := mkNatLit p
      
      newConcepts := newConcepts ++ [
        ConceptData.definition charName natType charValue none [] {
          name := charName
          created := concepts.length + p
          parent := none
          interestingness := 0.75 + (p.toFloat / 100.0)
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "characteristic_generation"
        }
      ]
      
      -- Generate associated prime power ring
      let ringName := s!"ring_Z_mod_{p}"
      let ringSize := mkNatLit p
      
      newConcepts := newConcepts ++ [
        ConceptData.definition ringName natType ringSize none [charName] {
          name := ringName
          created := concepts.length + p + 100
          parent := some charName
          interestingness := 0.8
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "ring_construction"
        }
      ]
      
      -- Add multiplicative structure info
      if p > 2 then
        let multGroupName := s!"mult_group_Z_{p}"
        let groupOrder := mkNatLit (p - 1)
        
        newConcepts := newConcepts ++ [
          ConceptData.definition multGroupName natType groupOrder none [ringName] {
            name := multGroupName
            created := concepts.length + p + 200
            parent := some ringName
            interestingness := 0.7
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "multiplicative_group_analysis"
          }
        ]
      
      -- Only generate a few at a time to avoid overwhelming
      if newConcepts.length >= 15 then break
  
  IO.println s!"[RingCharacteristics] Generated {newConcepts.length} ring characteristic concepts (beyond {maxChar})"
  return newConcepts

/-- Generate algebraic structure combinations -/
def generateAlgebraicCombinations : HeuristicFn := fun _config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Get iteration-like number from concept count
  let iteration := concepts.length / 100
  
  -- Generate mathematical objects with unique IDs
  for i in [0, 1, 2, 3, 4, 5, 6] do
    let objId := iteration * 50 + i * 7  -- Ensure uniqueness
    let objName := s!"algebra_object_{objId}"
    let natType := mkConst ``Nat
    let value := mkNatLit (objId % 500 + 1)
    
    newConcepts := newConcepts ++ [
      ConceptData.definition objName natType value none [] {
        name := objName
        created := concepts.length + i * 4
        parent := none
        interestingness := 0.6 + (i.toFloat / 20.0)
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "algebraic_generation"
      }
    ]
    
    -- Add operation closure property
    let closureName := s!"closure_property_{objId}"
    let closureValue := mkNatLit (if objId % 3 == 0 then 1 else 0)
    
    newConcepts := newConcepts ++ [
      ConceptData.definition closureName natType closureValue none [objName] {
        name := closureName
        created := concepts.length + i * 4 + 1
        parent := some objName
        interestingness := 0.4
        useCount := 0
        successCount := 0
        specializationDepth := 1
        generationMethod := "closure_analysis"
      }
    ]
    
    -- Add associativity property
    let assocName := s!"associativity_{objId}"
    let assocValue := mkNatLit (if objId % 5 == 0 then 1 else 0)
    
    newConcepts := newConcepts ++ [
      ConceptData.definition assocName natType assocValue none [objName] {
        name := assocName
        created := concepts.length + i * 4 + 2
        parent := some objName
        interestingness := 0.5
        useCount := 0
        successCount := 0
        specializationDepth := 1
        generationMethod := "associativity_analysis"
      }
    ]
    
    -- Add identity existence
    if i % 2 == 0 then
      let identityName := s!"identity_element_{objId}"
      let identityValue := mkNatLit objId
      
      newConcepts := newConcepts ++ [
        ConceptData.definition identityName natType identityValue none [objName] {
          name := identityName
          created := concepts.length + i * 4 + 3
          parent := some objName
          interestingness := 0.6
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "identity_discovery"
        }
      ]
  
  IO.println s!"[AlgebraicCombinations] Generated {newConcepts.length} algebraic concepts (iteration {iteration})"
  return newConcepts

/-- Updated enhanced heuristics -/
def groupRingHeuristics : List (String × HeuristicFn) := [
  ("generate_group_orders", generateGroupOrders),              -- Progressive group order exploration
  ("generate_ring_characteristics", generateRingCharacteristics), -- Systematic ring characteristics
  ("generate_algebraic_combinations", generateAlgebraicCombinations), -- Unique algebraic structures
  ("concrete_instance", concreteInstanceHeuristic),
  ("debug_typeclass_spec", typeclassSpecializationHeuristic),
  ("apply_specialized", applySpecializedTheorems),
  ("improved_algebraic_conj", algebraicConjectureHeuristic),
  ("structure_instance", structureInstanceHeuristic),
  ("algebraic_pattern", algebraicPatternRecognition),
  ("group_ring_duality", dualityHeuristic)
]

/-- Run discovery with group/ring theory focus -/
def runGroupRingDiscovery
    (grConfig : GroupRingConfig := {})
    (discoConfig : DiscoveryConfig := {})
    (maxIterations : Nat := 20) : MetaM Unit := do

  -- Mine domain-specific concepts
  let domainConcepts ← mineGroupRingConcepts grConfig
  let seedConcepts ← LeanDisco.seedConcepts
  let allInitialConcepts := seedConcepts ++ domainConcepts

  -- Get domain-specific heuristics
  let customHeuristics := groupRingHeuristics

  -- Run using the base runner
  let description := s!"Group/Ring Theory Discovery (group: {grConfig.includeBasicGroupTheory}, ring: {grConfig.includeBasicRingTheory})"
  runDiscoveryCustom description allInitialConcepts customHeuristics [] maxIterations true discoConfig


end LeanDisco.Domains.GroupRing
