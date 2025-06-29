import Lean
import Lean.Meta.Basic
import Lean.Elab.Command

 -- for mining!
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab

/-
# Eurisko-Inspired Discovery System for Lean

This system represents mathematical concepts, heuristics, and discovery tasks
as first-class objects in Lean, enabling automated mathematical discovery
with formal verification.
-/

namespace LeanDisco

/-- Configuration for controlling discovery -/
structure DiscoveryConfig where
  maxSpecializationDepth : Nat := 4
  maxConceptsPerIteration : Nat := 1000
  pruneThreshold : Float := 0.1
  deduplicateConcepts : Bool := true
  canonicalizeConcepts : Bool := true
  filterInternalProofs : Bool := true
  enableConjectures : Bool := true
  enablePatternRecognition : Bool := true
  enableDebugOutput : Bool := false

/-- Metadata for tracking concept performance and history -/
structure ConceptMetadata where
  name : String
  created : Nat
  parent : Option String
  interestingness : Float
  useCount : Nat
  successCount : Nat
  specializationDepth : Nat := 0
  generationMethod : String := "unknown"
  deriving Repr, BEq

/-- Core concept data with dependencies -/
inductive ConceptData where
  | definition :
    (name : String) →
    (type : Expr) →
    (value : Expr) →
    (canonicalValue : Option Expr) →
    (dependencies : List String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | theorem :
    (name : String) →
    (statement : Expr) →
    (proof : Expr) →
    (dependencies : List String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | conjecture :
    (name : String) →
    (statement : Expr) →
    (evidence : Float) →
    (metadata : ConceptMetadata) →
    ConceptData
  | pattern :
    (name : String) →
    (description : String) →
    (instances : List String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | heuristicRef :
    (name : String) →
    (description : String) →
    (metadata : ConceptMetadata) →
    ConceptData
  | taskRef :
    (name : String) →
    (goal : String) →
    (metadata : ConceptMetadata) →
    ConceptData

/-- Unique identifier for concepts -/
abbrev ConceptId := String

/-- Type for heuristic functions -/
abbrev HeuristicFn := DiscoveryConfig → List ConceptData → MetaM (List ConceptData)

/-- Type for evaluation functions -/
abbrev EvaluationFn := List ConceptData → MetaM Float

/-- Simple association list for storing heuristics -/
structure HeuristicRegistry where
  entries : List (ConceptId × HeuristicFn)

def HeuristicRegistry.empty : HeuristicRegistry := ⟨[]⟩

def HeuristicRegistry.insert (reg : HeuristicRegistry) (id : ConceptId) (fn : HeuristicFn) : HeuristicRegistry :=
  ⟨(id, fn) :: reg.entries⟩

def HeuristicRegistry.find? (reg : HeuristicRegistry) (id : ConceptId) : Option HeuristicFn :=
  reg.entries.lookup id

/-- Simple association list for storing evaluators -/
structure EvaluationRegistry where
  entries : List (ConceptId × EvaluationFn)

def EvaluationRegistry.empty : EvaluationRegistry := ⟨[]⟩

def EvaluationRegistry.insert (reg : EvaluationRegistry) (id : ConceptId) (fn : EvaluationFn) : EvaluationRegistry :=
  ⟨(id, fn) :: reg.entries⟩

def EvaluationRegistry.find? (reg : EvaluationRegistry) (id : ConceptId) : Option EvaluationFn :=
  reg.entries.lookup id

/-- Cache for previously attempted concept combinations -/
structure ConceptCache where
  attemptedApplications : List (String × String) := []  -- (function, argument) pairs
  attemptedSpecializations : List (String × String) := []  -- (theorem, value) pairs
  attemptedConjectures : List String := []  -- conjecture statements as strings
  normalizedExpressions : List (Expr × String) := []  -- (normalized expr, concept name) pairs

/-- Track failed proof attempts -/
structure FailedAttempt where
  statementStr : String
  attemptCount : Nat
  lastAttempt : Nat  -- iteration number

/-- Proof goal representing a target to prove -/
structure ProofGoal where
  name : String
  statement : Expr
  evidence : Float := 0.5
  priority : Float := 1.0
  dependencies : List String := []
  sorryCount : Nat := 0          -- Number of sorry holes in current best attempt
  missingLemmas : List String := []  -- Identified missing supporting lemmas
  iteration : Nat                -- When this goal was identified

/-- Track proof context and missing pieces -/
structure ProofContext where
  goals : List ProofGoal := []
  activeGoal : Option String := none
  recentFailures : List FailedAttempt := []
  targetConjectures : List String := []  -- High-priority conjectures to prove

/-- Result of applying a heuristic or evolution step -/
structure Discovery where
  newConcepts : List ConceptData
  modifiedConcepts : List ConceptData
  explanation : String

/-- Historical concept layers for better heuristic visibility -/
structure ConceptLayers where
  foundational : List ConceptData := []     -- Core seed concepts + early discoveries
  historical : List ConceptData := []       -- Concepts from 3+ iterations ago
  recent : List ConceptData := []           -- Concepts from last 2 iterations
  current : List ConceptData := []          -- Concepts from this iteration

/-- Knowledge base containing all discovered concepts -/
structure KnowledgeBase where
  concepts : List ConceptData
  layers : ConceptLayers := {}
  recentConcepts : List ConceptData         -- Kept for backward compatibility
  heuristics : HeuristicRegistry
  evaluators : EvaluationRegistry
  config : DiscoveryConfig
  iteration : Nat
  history : List (Nat × List String)
  cache : ConceptCache := {}
  failedProofs : List FailedAttempt := []
  proofContext : ProofContext := {}         -- Goal-directed proof tracking

/-- Context provided to heuristics for better discovery -/
structure HeuristicContext where
  config : DiscoveryConfig
  allConcepts : List ConceptData          -- All concepts (for backward compatibility)
  layers : ConceptLayers                  -- Layered access to concepts
  iteration : Nat                         -- Current iteration number
  failedProofs : List FailedAttempt       -- What didn't work before
  proofContext : ProofContext             -- Current proof goals and context


/-- Extract concept name -/
def getConceptName : ConceptData → String
  | ConceptData.definition n _ _ _ _ _ => n
  | ConceptData.theorem n _ _ _ _ => n
  | ConceptData.conjecture n _ _ _ => n
  | ConceptData.pattern n _ _ _ => n
  | ConceptData.heuristicRef n _ _ => n
  | ConceptData.taskRef n _ _ => n

/-- Get concept metadata -/
def getConceptMetadata : ConceptData → ConceptMetadata
  | ConceptData.definition _ _ _ _ _ m => m
  | ConceptData.theorem _ _ _ _ m => m
  | ConceptData.conjecture _ _ _ m => m
  | ConceptData.pattern _ _ _ m => m
  | ConceptData.heuristicRef _ _ m => m
  | ConceptData.taskRef _ _ m => m

/-- Update concept metadata -/
def updateConceptMetadata (c : ConceptData) (f : ConceptMetadata → ConceptMetadata) : ConceptData :=
  match c with
  | ConceptData.definition n t v cv d m => ConceptData.definition n t v cv d (f m)
  | ConceptData.theorem n s p d m => ConceptData.theorem n s p d (f m)
  | ConceptData.conjecture n s e m => ConceptData.conjecture n s e (f m)
  | ConceptData.pattern n d i m => ConceptData.pattern n d i (f m)
  | ConceptData.heuristicRef n d m => ConceptData.heuristicRef n d (f m)
  | ConceptData.taskRef n g m => ConceptData.taskRef n g (f m)

/-- Get concept value/statement -/
def getConceptExpr : ConceptData → Option Expr
  | ConceptData.definition _ _ v _ _ _ => some v
  | ConceptData.theorem _ s _ _ _ => some s
  | ConceptData.conjecture _ s _ _ => some s
  | _ => none

/-- Extract natural number literal from expression -/
partial def extractNatLiteral (e : Expr) : MetaM (Option Nat) := do
  try
    if e.hasLooseBVars then
      return none

    let e' ← whnf e
    match e' with
    | .const ``Nat.zero _ => return some 0
    | .app (.const ``Nat.succ _) n => do
      if let some n' ← extractNatLiteral n then
        return some (n' + 1)
      else
        return none
    | _ => return none
  catch _ => return none

def contains (s sub : String) : Bool :=
  (List.range (s.length - sub.length + 1)).any fun i =>
    (s.drop i |>.take sub.length) == sub


/-- Generate the next natural number -/
def generateNextNumber (kb : KnowledgeBase) : MetaM (Option ConceptData) := do
  let existingNumbers := kb.concepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ _ =>
      if n.startsWith "num_" then
        n.drop 4 |>.toNat?
      else if n == "zero" then some 0
      else if n == "one" then some 1
      else if n == "two" then some 2
      else none
    | _ => none

  let maxNum := existingNumbers.foldl max 0
  if maxNum < 10 then  -- Don't go too high
    let nextNum := maxNum + 1
    let numExpr := (List.range nextNum).foldl (fun acc _ =>
      mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)

    return some $ ConceptData.definition s!"num_{nextNum}"
      (mkConst ``Nat) numExpr none []
      { name := s!"num_{nextNum}"
        created := kb.iteration
        parent := none
        interestingness := 0.5
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "number_generation" }
  else
    return none

/-- Canonicalize a concept to its simplest form -/
def canonicalizeConcept (c : ConceptData) : MetaM ConceptData := do
  match c with
  | ConceptData.definition n t v cached deps meta =>
    if cached.isSome then
      return c  -- Already canonicalized
    else
      try
        let v' ← reduce v  -- Use reduce instead of just whnf
        -- Check if it's a natural number
        if let some num ← extractNatLiteral v' then
          let newName := s!"num_{num}"
          return ConceptData.definition newName t v' (some v') deps
            { meta with name := newName }
        else
          return ConceptData.definition n t v' (some v') deps meta
      catch _ =>
        -- If reduction fails, just cache the original value
        return ConceptData.definition n t v (some v) deps meta
  | _ => return c

-- Utility functions for proof goal management

/-- Add a new proof goal -/
def addProofGoal (context : ProofContext) (goal : ProofGoal) : ProofContext :=
  { context with 
    goals := context.goals ++ [goal]
    targetConjectures := 
      if goal.priority > 0.8 then context.targetConjectures ++ [goal.name]
      else context.targetConjectures }

/-- Update proof goal with new information -/
def updateProofGoal (context : ProofContext) (goalName : String) (update : ProofGoal → ProofGoal) : ProofContext :=
  { context with 
    goals := context.goals.map fun g => if g.name = goalName then update g else g }

/-- Get active proof targets -/
def getActiveTargets (context : ProofContext) : List ProofGoal :=
  context.goals.filter fun g => g.priority > 0.5

/-- Extract sorry holes from a proof expression -/
partial def countSorryHoles (expr : Expr) : Nat :=
  match expr with
  | Expr.const name _ => if name.toString = "sorry" then 1 else 0
  | Expr.app f arg => countSorryHoles f + countSorryHoles arg
  | Expr.lam _ _ body _ => countSorryHoles body
  | Expr.forallE _ _ body _ => countSorryHoles body
  | Expr.letE _ _ val body _ => countSorryHoles val + countSorryHoles body
  | _ => 0

/-- Convert high-evidence conjecture to proof goal -/
def conjectureToProofGoal (c : ConceptData) (iteration : Nat) : Option ProofGoal :=
  match c with
  | ConceptData.conjecture name statement evidence meta =>
    if evidence > 0.7 then  -- High evidence threshold
      some { name := name
             statement := statement
             evidence := evidence
             priority := evidence
             iteration := iteration }
    else none
  | _ => none

/-- Check if a concept name indicates an internal proof term -/
def isInternalProofTerm (name : String) : Bool :=
  ((name.splitOn "._proof_").length > 1) || ((name.splitOn ".match_").length > 1)

/-- Check if two expressions are definitionally equal -/
def exprsEqual (e1 e2 : Expr) : MetaM Bool := do
  try
    -- Instantiate metavariables first
    let e1' ← instantiateMVars e1
    let e2' ← instantiateMVars e2
    -- Check for loose bvars
    if e1'.hasLooseBVars || e2'.hasLooseBVars then
      return false
    isDefEq e1' e2'
  catch _ => return false

/-- Safely build `fun x : α => body x` where `body` may mention `x`. -/
def mkSafeLambda (n : Name) (type : Expr) (mkBody : Expr → MetaM Expr)
    : MetaM Expr := withLocalDecl n BinderInfo.default type fun x => do
  let body ← mkBody x          -- body *after* `x` is in scope
  mkLambdaFVars #[x] body

/-- Safely build `∀ x : α, body x` -/
def mkSafeForall (n : Name) (type : Expr) (mkBody : Expr → MetaM Expr)
    : MetaM Expr := withLocalDecl n BinderInfo.default type fun x => do
  let body ← mkBody x
  mkForallFVars #[x] body

/-- Conditional debug printing -/
def debugPrint (enabled : Bool) (msg : String) : IO Unit :=
  if enabled then IO.println msg else pure ()

/-- Context-aware deduplication that considers meaningful variations -/
def deduplicateWithWeakerNormalization (existing : List ConceptData) (newConcepts : List ConceptData) : MetaM (List ConceptData) := do
  let mut result : List ConceptData := []
  let mut duplicateCount := 0
  let mut keepCount := 0

  -- Build name-based cache first (lighter check)
  let existingNames := existing.map getConceptName

  -- Check each new concept
  for c in newConcepts do
    let cName := getConceptName c
    let mut shouldKeep := true
    let mut keepReason := "new"
    
    -- Level 1: Check for exact name duplicates
    if existingNames.contains cName then
      shouldKeep := false
      keepReason := "name_duplicate"
    -- Level 2: For patterns and non-expression concepts, only check names
    else match c with
      | ConceptData.pattern _ _ _ _ => 
        shouldKeep := true
      | ConceptData.conjecture _ _ _ _ =>
        shouldKeep := true
      | ConceptData.heuristicRef _ _ _ =>
        shouldKeep := true  
      | ConceptData.taskRef _ _ _ =>
        shouldKeep := true
      | _ =>
        -- Level 3: For expressions, do limited structural checking
        if let some expr := getConceptExpr c then
          try
            let weakNorm ← whnf expr
            -- Only reject if we find an exact syntactic match with same name pattern
            let mut foundExactMatch := false
            for existingC in existing do
              if let some existingExpr := getConceptExpr existingC then
                let existingWeakNorm ← whnf existingExpr
                if expr == existingExpr then
                  foundExactMatch := true
                  break
            shouldKeep := !foundExactMatch
            if foundExactMatch then
              keepReason := "exact_expression_duplicate"
          catch _ =>
            shouldKeep := true  -- Keep if normalization fails

    if shouldKeep then
      result := c :: result
      keepCount := keepCount + 1
    else
      duplicateCount := duplicateCount + 1
      debugPrint false s!"[DEDUP] Rejecting {cName}: {keepReason}"

  IO.println s!"[DEDUP] Kept {keepCount}, rejected {duplicateCount} from {newConcepts.length} candidates"
  return result.reverse

/-- Filter concepts by specialization depth -/
def filterByDepth (maxDepth : Nat) (concepts : List ConceptData) : List ConceptData :=
  concepts.filter fun c =>
    (getConceptMetadata c).specializationDepth ≤ maxDepth

/-- Filter out internal proof terms -/
def filterInternalTerms (concepts : List ConceptData) : List ConceptData :=
  concepts.filter fun c =>
    !isInternalProofTerm (getConceptName c)

/-- Apply all configured filters and cleanup with adaptive deduplication -/
def cleanupConcepts (config : DiscoveryConfig) (existing : List ConceptData) (newConcepts : List ConceptData) (iteration : Nat) : MetaM (List ConceptData) := do
  let mut cleaned := newConcepts

  debugPrint config.enableDebugOutput s!"[CLEANUP] Starting iteration {iteration} with {cleaned.length} concepts"

  -- Filter internal proof terms
  if config.filterInternalProofs then
    cleaned := filterInternalTerms cleaned
    debugPrint config.enableDebugOutput s!"[CLEANUP] After filterInternalTerms: {cleaned.length} concepts"

  -- Filter by depth
  cleaned := filterByDepth config.maxSpecializationDepth cleaned
  debugPrint config.enableDebugOutput s!"[CLEANUP] After filterByDepth: {cleaned.length} concepts"

  -- Canonicalize
  if config.canonicalizeConcepts then
    debugPrint config.enableDebugOutput s!"[CLEANUP] Starting canonicalization..."
    cleaned ← cleaned.mapM canonicalizeConcept
    debugPrint config.enableDebugOutput s!"[CLEANUP] After canonicalizeConcepts: {cleaned.length} concepts"

  -- WEAKER NORMALIZATION DEDUPLICATION instead of aggressive deduplication
  if config.deduplicateConcepts then
    debugPrint config.enableDebugOutput s!"[CLEANUP] Starting weaker normalization deduplication..."
    cleaned ← deduplicateWithWeakerNormalization existing cleaned
    debugPrint config.enableDebugOutput s!"[CLEANUP] After weaker deduplication: {cleaned.length} concepts"

  -- Special deduplication for patterns - check by name only
  let cleanedPatterns := cleaned.filter fun c => match c with
    | ConceptData.pattern name _ _ _ =>
      -- Just check if pattern name already exists
      !existing.any fun e => match e with
        | ConceptData.pattern ename _ _ _ => name == ename
        | _ => false
    | _ => true

  debugPrint config.enableDebugOutput s!"[CLEANUP] Returning {cleanedPatterns.length} concepts"
  return cleanedPatterns

/-- Update concept's interestingness score -/
def updateConceptScore (c : ConceptData) (score : Float) : ConceptData :=
  match c with
  | ConceptData.definition n t v cached d m =>
      ConceptData.definition n t v cached d { m with interestingness := score }
  | ConceptData.theorem n s p d m =>
      ConceptData.theorem n s p d { m with interestingness := score }
  | ConceptData.conjecture n s e m =>
      ConceptData.conjecture n s e { m with interestingness := score }
  | ConceptData.pattern n d i m =>
      ConceptData.pattern n d i { m with interestingness := score }
  | ConceptData.heuristicRef n d m =>
      ConceptData.heuristicRef n d { m with interestingness := score }
  | ConceptData.taskRef n g m =>
      ConceptData.taskRef n g { m with interestingness := score }

/-- Verify a definition is type-correct -/
def verifyDefinition (type : Expr) (value : Expr) : MetaM Bool := do
  try
    let valueType ← inferType value
    isDefEq valueType type
  catch e =>
    debugPrint false s!"[DEBUG] verifyDefinition failed"
    return false

/-- Verify a theorem by checking its proof -/
def verifyTheorem (statement : Expr) (proof : Expr) : MetaM Bool := do
  try
    let proofType ← inferType proof
    isDefEq proofType statement
  catch e =>
    debugPrint false s!"[DEBUG] verifyTheorem failed"
    return false

def safeIsDefEq (e₁ e₂ : Expr) : MetaM Bool := do
  try
    isDefEq e₁ e₂
  catch _ =>
    pure false

/-- Calculate a very rough structural similarity score. -/
partial def structuralSimilarity (e1 e2 : Expr) : MetaM Float := do
  try
    -- Safety check for loose bvars
    if e1.hasLooseBVars || e2.hasLooseBVars then
      return 0.0

    match (e1, e2) with
    | (.app f1 a1, .app f2 a2) =>
        return ((← structuralSimilarity f1 f2) +
                (← structuralSimilarity a1 a2)) / 2.0
    | (.const n1 _, .const n2 _) =>
        return if n1 == n2 then 1.0 else 0.0
    | (.forallE _ t1 b1 _, .forallE _ t2 b2 _) =>
        return ((← structuralSimilarity t1 t2) +
                (← structuralSimilarity b1 b2)) / 2.0
    | (.lam _ t1 b1 _, .lam _ t2 b2 _) =>
        return ((← structuralSimilarity t1 t2) +
                (← structuralSimilarity b1 b2)) / 2.0
    | _ =>
        return if ← safeIsDefEq e1 e2 then 0.5 else 0.0
  catch _ => return 0.0

/-- Expression size helper -/
partial def exprSize : Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ _ b _ => 1 + exprSize b
  | .forallE _ _ b _ => 1 + exprSize b
  | .letE _ _ v b _ => 1 + exprSize v + exprSize b
  | .lit _ => 1
  | .mdata _ e => 1 + exprSize e
  | .proj _ _ e => 1 + exprSize e

/-- Calculate evidence based on structural similarity and known theorems -/
def calculateConjectureEvidence (stmt : Expr) (kb : KnowledgeBase) : MetaM Float := do
  let mut evidence := 0.1  -- Base evidence

  -- Check structural similarity to proven theorems
  let mut maxSimilarity := 0.0
  for c in kb.concepts do
    match c with
    | ConceptData.theorem _ thmStmt _ _ _ =>
      let similarity ← structuralSimilarity stmt thmStmt
      maxSimilarity := max maxSimilarity similarity
    | _ => pure ()

  evidence := evidence + maxSimilarity * 0.3

  -- Boost evidence for simpler statements
  let complexity := exprSize stmt
  evidence := evidence + (1.0 / (1.0 + complexity.toFloat / 10.0)) * 0.3

  return min 1.0 evidence

/-- Enhanced conjecture proving with more tactics -/
def tryProveConjecture (stmt : Expr) : MetaM (Option Expr) := do
  try
    -- Try reflexivity for equality statements
    match stmt with
    | .app (.app (.app (.const ``Eq _) _) lhs) rhs =>
      if ← isDefEq lhs rhs then
        let proof ← mkAppM ``Eq.refl #[lhs]
        return some proof
      else
        -- Try reducing both sides
        let lhs' ← reduce lhs
        let rhs' ← reduce rhs
        if ← isDefEq lhs' rhs' then
          let proof ← mkAppM ``Eq.refl #[lhs']
          return some proof
        else
          return none
    | _ => return none
  catch _ => return none

/-- Check if a constant should be included based on filters -/
def shouldIncludeConstant (name : Name) (allowedPrefixes : List String) : Bool :=
  allowedPrefixes.any (·.isPrefixOf name.toString)

def shouldIncludeLib (env : Environment) (name : Name) (allowedLibs : List String) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx =>
      let modName := env.header.moduleNames[idx]!
      allowedLibs.any (·.isPrefixOf modName.toString)
  | none => false

/-- Mine concepts from the Lean environment -/
def mineEnvironment (allowedPrefixes : List String) (allowedLibs : List String) : MetaM (List ConceptData) := do
  let env ← getEnv
  let mut concepts := []

  let mkMeta (name : String) : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 0.5
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "mined"
  }

  for (name, info) in env.constants do
    if (shouldIncludeConstant name allowedPrefixes || shouldIncludeLib env name allowedLibs) && !isInternalProofTerm name.toString then
      match info with
      | .defnInfo val =>
        match val.safety with
        | .safe =>
          -- Check for loose bvars before adding
          if !val.type.hasLooseBVars && !val.value.hasLooseBVars then
            concepts := concepts ++ [ConceptData.definition
              name.toString val.type val.value none [] (mkMeta name.toString)]
        | _ => pure ()
      | .thmInfo val =>
        -- For theorems, we need to be more careful about the proof term
        -- The proof term might reference the theorem's parameters
        if !val.type.hasLooseBVars then
          -- Instead of using the raw proof value, use a constant reference
          let proofRef := mkConst name
          concepts := concepts ++ [ConceptData.theorem
            name.toString val.type proofRef [] (mkMeta name.toString)]
      | _ => pure ()

  return concepts

/-- Create initial mathematical concepts -/
def seedConcepts : MetaM (List ConceptData) := do
  let mut concepts := []

  let mkMeta (name : String) (method : String := "seed") : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := method
  }

  -- Natural numbers
  let natType := mkConst ``Nat

  -- Zero
  let zero := mkConst ``Nat.zero
  concepts := concepts ++ [ConceptData.definition "zero" natType zero none [] (mkMeta "zero")]

  -- Successor
  let succType ← mkArrow natType natType
  let succ := mkConst ``Nat.succ
  concepts := concepts ++ [ConceptData.definition "succ" succType succ none [] (mkMeta "succ")]

  -- One
  let one := mkApp succ zero
  concepts := concepts ++ [ConceptData.definition "one" natType one none ["zero", "succ"] (mkMeta "one")]

  -- Two (to help pattern recognition)
  let two := mkApp succ one
  concepts := concepts ++ [ConceptData.definition "two" natType two none ["one", "succ"] (mkMeta "two")]

  -- Addition
  let addType ← mkArrow natType (← mkArrow natType natType)
  let add := mkConst ``Nat.add
  concepts := concepts ++ [ConceptData.definition "add" addType add none [] (mkMeta "add")]

  -- Basic theorem: 0 = 0
  let zeroEqZero := mkApp3 (mkConst ``Eq [levelOne]) natType zero zero
  let zeroEqZeroProof := mkApp2 (mkConst ``Eq.refl [levelOne]) natType zero
  concepts := concepts ++ [ConceptData.theorem "zero_eq_zero" zeroEqZero zeroEqZeroProof ["zero"] (mkMeta "zero_eq_zero")]

  -- to test lemma application heuristic
  let addComm := mkConst ``Nat.add_comm
  concepts := concepts ++ [ConceptData.theorem
  "add_comm"  -- name
  (← inferType addComm)
  addComm      -- proof-term
  []
  (mkMeta "add_comm")]

  -- to test composition heuristic
  -- add 1 : Nat -> Nat
  let add1 ← withLocalDecl `x BinderInfo.default natType fun x => do
    let result := mkApp2 add one x
    mkLambdaFVars #[x] result
  let add1Type := mkForall `x BinderInfo.default natType natType
  concepts := concepts ++ [ConceptData.definition "add1" add1Type add1 none ["add", "one"] (mkMeta "add1")]

  -- add 2 : Nat -> Nat
  let add2 ← withLocalDecl `x BinderInfo.default natType fun x => do
    let result := mkApp2 add two x
    mkLambdaFVars #[x] result
  let add2Type := mkForall `x BinderInfo.default natType natType
  concepts := concepts ++ [ConceptData.definition "add2" add2Type add2 none ["add", "two"] (mkMeta "add2")]

  -- Add these concrete arithmetic facts
  concepts := concepts ++ [
  ConceptData.theorem "zero_add_zero"
    (mkApp3 (mkConst ``Eq [levelOne]) natType
      (mkApp2 add zero zero)
      zero)
    (mkApp2 (mkConst ``Eq.refl [levelOne]) natType zero)
    ["add", "zero"]
    (mkMeta "zero_add_zero" "arithmetic"),

  ConceptData.theorem "one_add_one_eq_two"
    (mkApp3 (mkConst ``Eq [levelOne]) natType
      (mkApp2 add one one)
      two)
    (mkApp2 (mkConst ``Eq.refl [levelOne]) natType two)
    ["add", "one", "two"]
    (mkMeta "one_add_one_eq_two" "arithmetic"),

  ConceptData.theorem "two_add_one_eq_three"
    (mkApp3 (mkConst ``Eq [levelOne]) natType
      (mkApp2 add two one)
      (mkApp succ two))
    (mkApp2 (mkConst ``Eq.refl [levelOne]) natType (mkApp succ two))
    ["add", "two", "one", "succ"]
    (mkMeta "two_add_one_eq_three" "arithmetic")
  ]

  return concepts

/-- Enhanced concept selection based on promise and diversity -/
def selectFocusConcepts (kb : KnowledgeBase) (maxConcepts : Nat) : List ConceptData :=
  -- Score concepts by multiple factors
  let scoredConcepts := kb.concepts.map fun c =>
    let meta := getConceptMetadata c
    let recencyBonus := if kb.recentConcepts.any (fun r => getConceptName r == getConceptName c) then 0.3 else 0.0
    let successBonus := meta.successCount.toFloat * 0.1
    let underexploredBonus := if meta.useCount < 3 then 0.2 else 0.0
    let depthPenalty := meta.specializationDepth.toFloat * 0.1
    let patternBonus := match c with
      | ConceptData.pattern _ _ instances _ => instances.length.toFloat * 0.05
      | _ => 0.0

    let score := meta.interestingness + recencyBonus + successBonus +
                 underexploredBonus + patternBonus - depthPenalty
    (c, score)

  -- Sort by score and take top concepts
  let sorted := scoredConcepts.toArray.qsort (·.2 > ·.2)

  -- Ensure diversity by limiting concepts of the same type
  Id.run do
    let mut selected : List ConceptData := []
    let mut typeCount : List (String × Nat) := []

    for (c, _) in sorted do
      let conceptType := match c with
        | ConceptData.definition _ _ _ _ _ m => m.generationMethod
        | ConceptData.theorem _ _ _ _ m => "theorem"
        | ConceptData.conjecture _ _ _ _ => "conjecture"
        | ConceptData.pattern _ _ _ _ => "pattern"
        | _ => "other"

      let currentCount := (typeCount.lookup conceptType).getD 0
      if currentCount < maxConcepts / 4 then  -- Limit each type
        selected := selected ++ [c]
        typeCount := typeCount.filter (·.1 != conceptType) ++ [(conceptType, currentCount + 1)]

      if selected.length >= maxConcepts then
        break

    selected

/-- Apply evolution heuristics to generate new concepts -/
def evolve (kb : KnowledgeBase) : MetaM (List Discovery) := do
  let heuristicRefs := kb.concepts.filterMap fun c => match c with
    | ConceptData.heuristicRef name _ meta => some (name, meta)
    | _ => none

  let mut discoveries := []

  -- Generate new numbers every other iteration
  if kb.iteration % 2 == 0 then
    if let some newNum ← generateNextNumber kb then
      discoveries := discoveries ++ [Discovery.mk [newNum] [] "Generated next number"]

  -- Enhanced visibility: Provide all concepts to heuristics instead of limited focused concepts
  -- This solves the main issue - heuristics now see the full discovery history
  let allConceptsWithLayers := kb.concepts
  
  IO.println s!"[DEBUG] Providing enhanced visibility to heuristics: {allConceptsWithLayers.length} total concepts (foundational={kb.layers.foundational.length}, historical={kb.layers.historical.length}, recent={kb.layers.recent.length}, current={kb.layers.current.length})"

  -- Prioritize goal-directed heuristics over stochastic exploration
  let prioritizedHeuristics := heuristicRefs.partition fun (name, _) => 
    name ∈ ["goal_directed", "backwards_reasoning", "pattern_guided", "specialization", "application"]
  let (highPriorityRefs, regularRefs) := prioritizedHeuristics
  
  -- Apply high-priority (goal-directed) heuristics first
  let orderedRefs := highPriorityRefs ++ regularRefs.filter fun (name, _) => name ≠ "stochastic_exploration"
  
  -- Only apply stochastic exploration if we haven't found enough concepts after 2 iterations
  let finalRefs := if kb.iteration > 2 && discoveries.length < 3 then
    orderedRefs ++ regularRefs.filter fun (name, _) => name = "stochastic_exploration"
  else
    orderedRefs
  
  IO.println s!"[DEBUG] Prioritized heuristic order: {finalRefs.map Prod.fst}"
  for (name, meta) in finalRefs do
    if let some heuristic := kb.heuristics.find? name then
      try
        let newConcepts ← heuristic kb.config allConceptsWithLayers

        IO.println s!"[HEURISTIC] {name} generated {newConcepts.length} raw concepts"
        if newConcepts.length > 0 && newConcepts.length <= 5 then
          for c in newConcepts do
            IO.println s!"  - {getConceptName c} ({(getConceptMetadata c).generationMethod})"

        -- Add more detailed debugging here
        for c in newConcepts do
          if let some expr := getConceptExpr c then
            if expr.hasLooseBVars then
              debugPrint kb.config.enableDebugOutput s!"[DEBUG] WARNING: Concept {getConceptName c} from {name} has loose bvars!"

        -- Clean up new concepts against ALL existing concepts
        let cleanedConcepts ← cleanupConcepts kb.config kb.concepts newConcepts kb.iteration

        if newConcepts.length > 0 then
          IO.println s!"[CLEANUP] {name}: {newConcepts.length} → {cleanedConcepts.length} concepts after cleanup"
          if cleanedConcepts.length == 0 && newConcepts.length > 0 then
            IO.println s!"  [WARNING] All concepts from {name} were filtered out!"

        -- Verify all new concepts
        let mut verifiedConcepts := []
        for concept in cleanedConcepts do
          -- Add safety check before verification
          let shouldVerify := match concept with
            | ConceptData.definition _ t v _ _ _ =>
              !t.hasLooseBVars && !v.hasLooseBVars
            | ConceptData.theorem _ s p _ _ =>
              !s.hasLooseBVars && !p.hasLooseBVars
            | _ => true

          if shouldVerify then
            match concept with
            | ConceptData.definition _ t v _ _ _ =>
              if ← verifyDefinition t v then
                verifiedConcepts := verifiedConcepts ++ [concept]
            | ConceptData.theorem _ s p _ _ =>
              if ← verifyTheorem s p then
                verifiedConcepts := verifiedConcepts ++ [concept]
            | ConceptData.conjecture _ _ _ _ =>
              verifiedConcepts := verifiedConcepts ++ [concept]
            | ConceptData.pattern _ _ _ _ =>
              verifiedConcepts := verifiedConcepts ++ [concept]
            | _ => verifiedConcepts := verifiedConcepts ++ [concept]
          else
            debugPrint kb.config.enableDebugOutput s!"[DEBUG] Skipping verification of {getConceptName concept} due to loose bvars"

        if cleanedConcepts.length > 0 then
          IO.println s!"[VERIFY] {name}: {cleanedConcepts.length} → {verifiedConcepts.length} concepts after verification"
          if verifiedConcepts.length == 0 && cleanedConcepts.length > 0 then
            IO.println s!"  [WARNING] All concepts from {name} failed verification!"

        -- Limit number of concepts per heuristic
        let limitedConcepts := verifiedConcepts.take kb.config.maxConceptsPerIteration

        if limitedConcepts.length > 0 then
          discoveries := discoveries ++ [Discovery.mk limitedConcepts [] s!"Applied heuristic {meta.name}"]
          IO.println s!"[SUCCESS] {name} contributed {limitedConcepts.length} concepts to discoveries"
      catch err =>
        let msg := err.toMessageData
        logInfo m!"[DEBUG] Error in heuristic {name}: {msg}"
        pure ()

  return discoveries

/-- Evaluate discoveries using task-based criteria -/
def evaluate (kb : KnowledgeBase) (discoveries : List Discovery) : MetaM (List ConceptData) := do
  let taskRefs := kb.concepts.filterMap fun c => match c with
    | ConceptData.taskRef name _ meta => some (name, meta)
    | _ => none

  let mut evaluatedConcepts := []

  for discovery in discoveries do
    for concept in discovery.newConcepts do
      let mut totalScore := 0.0
      let mut taskCount := 0

      for (name, _) in taskRefs do
        if let some eval := kb.evaluators.find? name then
          try
            let score ← eval (kb.concepts ++ [concept])
            totalScore := totalScore + score
            taskCount := taskCount + 1
          catch _ =>
            pure ()

      let avgScore := if taskCount > 0 then totalScore / taskCount.toFloat else 0.5
      let updatedConcept := updateConceptScore concept avgScore

      if avgScore > kb.config.pruneThreshold then
        evaluatedConcepts := evaluatedConcepts ++ [updatedConcept]

  return evaluatedConcepts

/-- Show discovered concepts more clearly -/
def showDiscoveredConcepts (concepts : List ConceptData) (showDetails : Bool := true) : MetaM Unit := do
  -- Group by type
  let conjectures := concepts.filter fun c => match c with
    | ConceptData.conjecture _ _ _ _ => true | _ => false
  let newTheorems := concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ m => m.generationMethod != "mined" | _ => false
  let patterns := concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true | _ => false
  let applications := concepts.filter fun c => match c with
    | ConceptData.definition _ _ _ _ _ m => m.generationMethod == "application" | _ => false
  let numbers := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => m.generationMethod == "number_generation" | _ => false
  let compositions := concepts.filter fun c => match c with
    | ConceptData.definition _ _ _ _ _ m => m.generationMethod == "composition" | _ => false

  if numbers.length > 0 then
    IO.println s!"\n🔢 New Numbers ({numbers.length}):"
    for n in numbers do
      IO.println s!"  - {getConceptName n}"

  if conjectures.length > 0 then
    IO.println s!"\n🔮 Conjectures ({conjectures.length}):"
    for c in conjectures.take 5 do
      match c with
      | ConceptData.conjecture name stmt evidence _ =>
        IO.println s!"  - {name}"
        IO.println s!"    Evidence: {evidence}"
      | _ => pure ()
    if conjectures.length > 5 then
      IO.println s!"  ... and {conjectures.length - 5} more"

  if newTheorems.length > 0 then
    IO.println s!"\n✓ Proven Theorems ({newTheorems.length}):"
    for t in newTheorems.take 5 do
      match t with
      | ConceptData.theorem name _ _ _ meta =>
        IO.println s!"  - {name}"
        IO.println s!"    Method: {meta.generationMethod}"
      | _ => pure ()

  if patterns.length > 0 then
    IO.println s!"\n🔍 Patterns ({patterns.length}):"
    for p in patterns do
      match p with
      | ConceptData.pattern name desc instances _ =>
        IO.println s!"  - {name}: {desc}"
        if showDetails && instances.length > 0 then
          IO.println s!"    Examples: {instances.take 3}"
      | _ => pure ()

  if applications.length > 0 then
    IO.println s!"\n🔧 Function Applications ({applications.length}):"
    for a in applications.take 3 do
      let name := getConceptName a
      IO.println s!"  - {name}"

  if compositions.length > 0 then
    IO.println s!"\n🔗 Function Compositions ({compositions.length}):"
    for c in compositions.take 3 do
      let name := getConceptName c
      IO.println s!"  - {name}"

/-- Update cache with new attempts -/
def updateCache (cache : ConceptCache) (newConcepts : List ConceptData) : ConceptCache :=
  let newApplications := newConcepts.filterMap fun c => match c with
    | ConceptData.definition n _ _ _ _ m =>
      if m.generationMethod == "application" then
        let parts := n.splitOn "_applied_to_"
        if parts.length == 2 then some (parts[0]!, parts[1]!)
        else none
      else none
    | _ => none

  let newSpecializations := newConcepts.filterMap fun c => match c with
    | ConceptData.theorem n _ _ _ m =>
      if m.generationMethod == "specialization" then
        let parts := n.splitOn "_spec_"
        if parts.length == 2 then some (parts[0]!, parts[1]!)
        else none
      else none
    | _ => none

  { cache with
    attemptedApplications := cache.attemptedApplications ++ newApplications
    attemptedSpecializations := cache.attemptedSpecializations ++ newSpecializations
  }

/-- Main discovery loop -/
partial def discoveryLoop (kb : KnowledgeBase) (maxIterations : Nat) : MetaM KnowledgeBase := do
  if kb.iteration >= maxIterations then
    return kb

  IO.println s!"\n--- Iteration {kb.iteration + 1} ---"

  -- Show what we're focusing on
  if kb.recentConcepts.length > 0 then
    IO.println s!"Building on {kb.recentConcepts.length} recent discoveries:"
    for c in kb.recentConcepts.take 5 do
      IO.println s!"  - {getConceptName c}"

  let discoveries ← evolve kb
  let mut allNewConcepts := []
  for discovery in discoveries do
    allNewConcepts := allNewConcepts ++ discovery.newConcepts

  let evaluatedConcepts ← evaluate kb discoveries

  if evaluatedConcepts.length > 0 then
    IO.println s!"{evaluatedConcepts.length} new concepts discovered this iteration"

    showDiscoveredConcepts evaluatedConcepts

    -- Count by method manually
    IO.println s!"\n📊 Discovery Summary:"
    let methods := ["specialization", "application", "conjecture", "pattern_recognition",
                    "lemma_application", "number_generation", "composition", "pattern_extension"]
    for method in methods do
      let count := evaluatedConcepts.filter (fun c => (getConceptMetadata c).generationMethod == method) |>.length
      if count > 0 then
        IO.println s!"  {method}: {count} concepts"
  else
    IO.println "No new concepts discovered this iteration"

  -- Try to prove conjectures
  let mut provenConjectures := []
  let mut allConjectures := kb.concepts ++ evaluatedConcepts

  -- Remove conjectures that get proved
  let mut remainingConcepts := []

  for c in allConjectures do
    match c with
    | ConceptData.conjecture name stmt _ meta =>
      -- Check if we've failed this before
      let failedBefore := kb.failedProofs.any fun fa =>
        fa.statementStr == toString stmt && fa.attemptCount >= 3

      if !failedBefore then
        if let some proof ← tryProveConjecture stmt then
          IO.println s!"  ✓ Proved conjecture: {name}"
          let thm := ConceptData.theorem name stmt proof []
            { meta with generationMethod := "conjecture_proved" }
          provenConjectures := provenConjectures ++ [thm]

          -- Reward parent concepts for successful proof
          if let some parentName := meta.parent then
            remainingConcepts := remainingConcepts.map fun c' =>
              if getConceptName c' == parentName then
                updateConceptMetadata c' fun m =>
                  { m with successCount := m.successCount + 1 }
              else c'
        else
          -- Track failed attempt
          let stmtStr := toString stmt
          let mut newFailedProofs := kb.failedProofs
          match kb.failedProofs.find? (·.statementStr == stmtStr) with
          | some fa =>
            newFailedProofs := newFailedProofs.filter (·.statementStr != stmtStr) ++
              [{ fa with attemptCount := fa.attemptCount + 1, lastAttempt := kb.iteration }]
          | none =>
            newFailedProofs := newFailedProofs ++
              [{ statementStr := stmtStr, attemptCount := 1, lastAttempt := kb.iteration }]

          -- Keep unproven conjectures
          remainingConcepts := remainingConcepts ++ [c]
      else
        -- Skip conjectures we've failed too many times
        pure ()
    | _ =>
      remainingConcepts := remainingConcepts ++ [c]

  -- Update cache with new concepts
  let newCache := updateCache kb.cache evaluatedConcepts

  -- Update concept layers with new discoveries (simplified for now)
  let newConceptsForLayers := evaluatedConcepts ++ provenConjectures
  let updatedLayers : ConceptLayers := {
    foundational := kb.layers.foundational
    historical := kb.layers.historical ++ kb.layers.recent
    recent := newConceptsForLayers
    current := newConceptsForLayers
  }

  let newKb : KnowledgeBase := {
    concepts := remainingConcepts ++ provenConjectures
    layers := updatedLayers
    recentConcepts := evaluatedConcepts ++ provenConjectures
    heuristics := kb.heuristics
    evaluators := kb.evaluators
    config := kb.config
    iteration := kb.iteration + 1
    history := kb.history ++ [(kb.iteration, (evaluatedConcepts ++ provenConjectures).map getConceptName)]
    cache := newCache
    failedProofs := kb.failedProofs
  }

  discoveryLoop newKb maxIterations

/--
Heuristic: apply any mined Eq-theorem whose left-hand side matches another concept's expression,
producing new theorems `thName_on_targetName` via lemma application.
Enhanced: Now has access to full discovery history through concept layers.
-/
def lemmaApplicationHeuristic : HeuristicFn := fun config concepts => do
  let mut out : List ConceptData := []
  for c in concepts do
    match c with
    | ConceptData.theorem thName stmt proof deps meta => do
      let fn := stmt.getAppFn
      if fn.isConstOf ``Eq then
        let argsList := stmt.getAppArgs.toList
        match argsList with
        | α :: lhs :: rhs :: [] =>
          let lemmaName := Name.mkStr Name.anonymous thName
          for tgt in concepts do
            if let some tgtExpr := getConceptExpr tgt then
              try
                if ← isDefEq lhs tgtExpr then
                  debugPrint false s!"[DEBUG][lemma_application] applying {thName} to {getConceptName tgt}"
                  let eqConst := mkConst ``Eq [levelOne]
                  let newStmt := mkApp3 eqConst α tgtExpr rhs

                  let newProof := proof
                  let newName := thName ++ "_on_" ++ getConceptName tgt
                  let newMeta := { meta with
                    name := newName,
                    parent := some thName,
                    generationMethod := "lemma_application"
                  }
                  out := out ++ [ConceptData.theorem newName newStmt newProof deps newMeta]
              catch e =>
                debugPrint false s!"[DEBUG][lemma_application] isDefEq failed"
                pure ()
        | _ => pure ()
    | _ => pure ()
  return out

/-- Use discovered patterns to guide new concept generation -/
def patternGuidedHeuristic : HeuristicFn := fun config concepts => do
  let patterns := concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true
    | _ => false

  let mut newConcepts := []

  for pattern in patterns do
    match pattern with
    | ConceptData.pattern "natural_number_sequence" _ instances _ =>
      -- If we have a sequence pattern, try to extend it
      let maxNum := instances.foldl (fun acc inst =>
        if inst.startsWith "num_" then
          max acc ((inst.drop 4).toNat?.getD 0)
        else if inst == "zero" then max acc 0
        else if inst == "one" then max acc 1
        else if inst == "two" then max acc 2
        else acc
      ) 0

      -- Generate the next few numbers in the sequence
      for i in [maxNum + 1:min (maxNum + 3) 15] do  -- Increased limit
        let numExpr := (List.range i).foldl (fun acc _ =>
          mkApp (mkConst ``Nat.succ) acc) (mkConst ``Nat.zero)
        let newConcept := ConceptData.definition s!"num_{i}"
          (mkConst ``Nat) numExpr none []
          { name := s!"num_{i}", created := 0, parent := some "natural_number_sequence",
            interestingness := 0.6, useCount := 0, successCount := 0,
            specializationDepth := 0, generationMethod := "pattern_extension" }
        newConcepts := newConcepts ++ [newConcept]

    | ConceptData.pattern name desc instances meta =>
      -- For function iteration patterns, try to continue the iteration
      if name.endsWith "_iteration_pattern" then
        -- Extract function name
        let funcName := name.dropRight "_iteration_pattern".length
        -- Find the function
        if let some funcConcept := concepts.find? fun c =>
          getConceptName c == funcName then
          match funcConcept with
          | ConceptData.definition _ _ funcVal _ _ _ =>
            -- Find highest iteration
            let maxIter := instances.foldl (fun acc inst =>
              if inst.startsWith s!"{funcName}_applied_to_" then
                let parts := inst.splitOn "_applied_to_"
                if parts.length >= 2 then
                  let lastPart := parts.getLast!
                  if lastPart.startsWith s!"{funcName}_applied_to_" then
                    acc + 1
                  else acc
                else acc
              else acc
            ) 0

            if maxIter < 5 then  -- Don't go too deep
              -- Find the last application and apply function again
              if let some lastApp := concepts.find? fun c =>
                instances.contains (getConceptName c) then
                if let some lastExpr := getConceptExpr lastApp then
                  let newApp := mkApp funcVal lastExpr
                  let newName := s!"{funcName}_iter_{maxIter + 1}"
                  let newType ← inferType newApp
                  newConcepts := newConcepts ++ [
                    ConceptData.definition newName newType newApp none [funcName]
                      { name := newName, created := 0, parent := some name,
                        interestingness := 0.5, useCount := 0, successCount := 0,
                        specializationDepth := maxIter + 1, generationMethod := "pattern_extension" }
                  ]
          | _ => pure ()
    | _ => pure ()

  return newConcepts

/-- Pattern recognition heuristic: identify mathematical patterns -/
def patternRecognitionHeuristic : HeuristicFn := fun config concepts => do
  if !config.enablePatternRecognition then
    return []

  let mut patterns := []

  try
    -- Look for arithmetic sequences
    let numbers := concepts.filterMap fun c => match c with
      | ConceptData.definition n _ v _ _ m =>
        if n.startsWith "num_" || n == "zero" || n == "one" || n == "two" then
            some (n, v, m)
        else none
      | _ => none

    if numbers.length >= 3 then
      -- Check if we have 0, 1, 2...
      let mut hasSequence := false
      let mut sequenceNames := []

      for (n, _, _) in numbers do
        if n == "zero" || n == "one" || n == "two" || n.startsWith "num_" then
          sequenceNames := sequenceNames ++ [n]
          hasSequence := true

      if hasSequence && sequenceNames.length >= 3 then
        let patternMeta := {
          name := "natural_number_sequence"
          created := 0
          parent := none
          interestingness := 0.8
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "pattern_recognition"
        }
        patterns := patterns ++ [
          ConceptData.pattern
            "natural_number_sequence"
            "Sequence: 0, 1, 2, ... (natural numbers via successor)"
            sequenceNames
            patternMeta
        ]

    -- Look for function iteration patterns
    let applications := concepts.filter fun c => match c with
      | ConceptData.definition n _ v _ _ m =>
        m.generationMethod == "application" && ((n.splitOn "_applied_to_").length > 1) && !v.hasLooseBVars
      | _ => false

    if applications.length >= 3 then
      -- Check for repeated application of same function
      let mut functionApplications : List (String × List String) := []

      for c in applications do
        let name := getConceptName c
        let parts := name.splitOn "_applied_to_"
        if parts.length > 0 then
          let func := parts.head!
          match functionApplications.find? (·.1 == func) with
          | some (_, apps) =>
            functionApplications := functionApplications.filter (·.1 != func) ++ [(func, apps ++ [name])]
          | none =>
            functionApplications := functionApplications ++ [(func, [name])]

      for (func, apps) in functionApplications do
        if apps.length >= 2 then
          let patternMeta := {
            name := s!"{func}_iteration_pattern"
            created := 0
            parent := none
            interestingness := 0.7
            useCount := 0
            successCount := 0
            specializationDepth := 0
            generationMethod := "pattern_recognition"
          }
          patterns := patterns ++ [
            ConceptData.pattern
              s!"{func}_iteration_pattern"
              s!"Repeated application of {func}"
              apps
              patternMeta
          ]
  catch _ =>
    -- If anything fails, just return what we have so far
    pure ()

  return patterns

/-- Conjecture generation heuristic -/
def conjectureGenerationHeuristic : HeuristicFn := fun config concepts => do
    if !config.enableConjectures then
      return []

    -- Build helper collections ONCE
    let theorems  := concepts.filterMap fun c => match c with
      | ConceptData.theorem n s p d m =>
          if !((n.splitOn "_spec_").length ≤ 1) then
            some (n, s, p, d, m) else none
      | _ => none

    let functions : List (String × Expr × Expr) := concepts.filterMap fun c => match c with
      | ConceptData.definition n t v _ _ _ =>
          if t.isForall && !((n.splitOn "_applied_").length > 1) then
            some (n, v, t) else none
      | _ => none

    let kb : KnowledgeBase := {
      concepts := concepts
      layers := {}
      recentConcepts := []
      heuristics := HeuristicRegistry.empty
      evaluators := EvaluationRegistry.empty
      config     := config
      iteration  := 0
      history    := []
      cache      := {}
      failedProofs := []
    }

    -- PATTERN 1: Composition: functions × functions
    let mut conjectures := []
    for (f₁, v₁, t₁) in functions do
      for (f₂, v₂, t₂) in functions do
        if f₁ ≠ f₂ ∧ f₁.length < 10 ∧ f₂.length < 10 then
          match (t₁, t₂) with
          | ((.forallE _ A₁ _ _), (.forallE _ _  B₂ _)) =>
              if ← isDefEq B₂ A₁ then
                let natTy := mkConst ``Nat
                let z     := mkConst ``Nat.zero
                let one   := mkApp (mkConst ``Nat.succ) z
                let comp0 := mkApp v₁ (mkApp v₂ z)
                let candidates : List (Nat × Expr) := [ (0, mkApp v₁ z), (1, mkApp v₂ z), (2, z), (3, one) ]
                for (idx, cand) in candidates do
                  let stmt := mkApp3 (mkConst ``Eq [levelOne]) natTy comp0 cand
                  let ev   ← calculateConjectureEvidence stmt kb
                  conjectures := conjectures ++
                    [ ConceptData.conjecture
                        s!"{f₁}_comp_{f₂}_eq_{idx}"
                        stmt ev
                        { name               := s!"{f₁}_comp_{f₂}_eq_{idx}"
                          created            := 0
                          parent             := none
                          interestingness    := 0.7
                          useCount           := 0
                          successCount       := 0
                          specializationDepth:= 1
                          generationMethod   := "composition_pattern" } ]
          | _ => pure ()

    -- PATTERN 2: Preservation: theorems × functions (once)
    for (thm, _, _, _, _) in theorems do
      if contains thm "eq" ∨ contains thm "comm" ∨ contains thm "assoc" then
        for (fn, fv, ft) in functions do
          match ft with
          | Expr.forallE _ (.const ``Nat _) (.const ``Nat _) _ => do
              if !fv.hasLooseBVars then
                let natTy := mkConst ``Nat
                let z     := mkConst ``Nat.zero
                let one   := mkApp (mkConst ``Nat.succ) z
                let stmt  := mkApp3 (mkConst ``Eq [levelOne])
                                    natTy (mkApp fv z) (mkApp fv one)
                let ev ← calculateConjectureEvidence stmt kb
                conjectures := conjectures ++
                  [ ConceptData.conjecture
                      s!"{fn}_preserves_{thm}_maybe"
                      stmt ev
                      { name := s!"{fn}_preserves_{thm}_maybe",
                        created := 0, parent := some thm,
                        interestingness := 0.5, useCount := 0, successCount := 0,
                        specializationDepth := 1,
                        generationMethod := "preservation_pattern" } ]
          | _ => pure ()

    -- PATTERN 3: Fixed‑point & Homomorphism: functions (once)
    for (fn, fv, ft) in functions do
      match ft with
      | Expr.forallE _ (.const ``Nat _) (.const ``Nat _) _ => do
          if !fv.hasLooseBVars then
            -- 3a. fixed point f 0 = 0
            let natTy := mkConst ``Nat
            let z     := mkConst ``Nat.zero
            let stmt1 := mkApp3 (mkConst ``Eq [levelOne])
                                natTy (mkApp fv z) z
            let ev1 ← calculateConjectureEvidence stmt1 kb
            conjectures := conjectures ++
              [ ConceptData.conjecture
                  s!"{fn}_fixed_point_zero"
                  stmt1 ev1
                  { name := s!"{fn}_fixed_point_zero",
                    created := 0, parent := none,
                    interestingness := 0.6, useCount := 0, successCount := 0,
                    specializationDepth := 1,
                    generationMethod := "fixed_point_search" } ]

            -- 3b. homomorphism  ∀ x y, f(x+y)=f x + f y
            let stmt2 ← Lean.Meta.withLocalDecl `x .default natTy fun xVar => do
              Lean.Meta.withLocalDecl `y .default natTy fun yVar => do
                let add := mkConst ``Nat.add
                let eq  := mkConst ``Eq  [levelOne]
                let fxy := mkApp fv (mkApp2 add xVar yVar)
                let rhs := mkApp2 add (mkApp fv xVar) (mkApp fv yVar)
                let body := mkApp3 eq natTy fxy rhs
                Lean.Meta.mkForallFVars #[xVar,yVar] body
            let ev2 ← calculateConjectureEvidence stmt2 kb
            conjectures := conjectures ++
              [ ConceptData.conjecture
                  s!"{fn}_homomorphism"
                  stmt2 ev2
                  { name := s!"{fn}_homomorphism",
                    created := 0, parent := some fn,
                    interestingness := 0.7, useCount := 0, successCount := 0,
                    specializationDepth := 1,
                    generationMethod := "homomorphism_pattern" } ]
      | _ => pure ()

    -- PATTERN 4: Concrete add_comm conjecture
    let nums := concepts.filterMap fun c => match c with
      | ConceptData.definition n _ v _ _ _ =>
          if n == "zero" ∨ n == "one" ∨ n == "two" ∨ n.startsWith "num_" then
            some (n,v) else none
      | _ => none
    match nums with
    | (n₁,v₁) :: (n₂,v₂) :: _ =>
        if let some (ConceptData.definition _ _ addFn _ _ _) :=
            concepts.find? (fun c => getConceptName c = "add") then
          let natTy := mkConst ``Nat
          let stmt  := mkApp3 (mkConst ``Eq [levelOne]) natTy
                              (mkApp2 addFn v₁ v₂) (mkApp2 addFn v₂ v₁)
          let ev ← calculateConjectureEvidence stmt kb
          conjectures := conjectures ++
            [ ConceptData.conjecture
                s!"add_comm_{n₁}_{n₂}"
                stmt ev
                { name := s!"add_comm_{n₁}_{n₂}", created := 0,
                  parent := none, interestingness := 0.3,
                  useCount := 0, successCount := 0, specializationDepth := 1,
                  generationMethod := "commutativity"} ]
    | _ => pure ()

    debugPrint false s!"[DEBUG] Total conjectures generated: {conjectures.length}"
    return conjectures

/-- Specialization heuristic: create specific instances -/
def specializationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  -- Find universal theorems
  for c in concepts do
    match c with
    | ConceptData.theorem name stmt proof deps meta =>
      -- Skip if already deeply specialized
      if meta.specializationDepth >= config.maxSpecializationDepth then
        continue

      -- Skip theorems that are already specializations
      if (name.splitOn "_spec_").length > 1 then
        continue

      -- Check if it's a forall statement
      match ← whnf stmt with
      | .forallE _ varType body _ =>
        -- Try to specialize with known terms of the right type
        let mut specializationCount := 0
        for c2 in concepts do
          if specializationCount >= 5 then  -- Limit specializations per theorem
            break

          match c2 with
          | ConceptData.definition defName _ defValue _ _ defMeta =>
            -- Skip complex definitions for specialization
            if defMeta.specializationDepth > 1 then
              continue

            let defType ← inferType defValue
            if ← isDefEq defType varType then
              -- Create specialized theorem
              let specStmt := body.instantiate1 defValue
              let specProof := mkApp proof defValue
              let specName := s!"{name}_spec_{defName}"
              let newMeta := { meta with
                name := specName
                parent := some name
                interestingness := 0.0
                specializationDepth := meta.specializationDepth + 1
                generationMethod := "specialization"
              }
              newConcepts := newConcepts ++ [
                ConceptData.theorem specName specStmt specProof (deps ++ [defName]) newMeta
              ]
              specializationCount := specializationCount + 1
          | _ => pure ()
      | _ => pure ()
    | _ => pure ()

  return newConcepts

/-- Function application heuristic with caching -/
def applicationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  -- Enhanced: Separate concepts by generation method for better targeting
  let seedFunctions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if !t.hasLooseBVars && !v.hasLooseBVars && (m.generationMethod == "seed" || m.generationMethod == "mined") && t.isForall then
        some (n, t, v, d, m)
      else none
    | _ => none

  let allArgs := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if !t.hasLooseBVars && !v.hasLooseBVars && m.specializationDepth <= 1 then
        some (n, t, v, d, m)
      else none
    | _ => none

  IO.println s!"[APPLICATION] Found {seedFunctions.length} seed functions, {allArgs.length} potential arguments"

  -- Strategy 1: Apply seed functions to all suitable arguments
  for (fname, ftype, fvalue, fdeps, fmeta) in seedFunctions do
    match ← whnf ftype with
    | .forallE _ argType _ _ =>
      let mut applicationCount := 0
      for (aname, _, avalue, adeps, ameta) in allArgs do
        if applicationCount >= 5 then  -- Increased limit for seed functions
          break

        let proposedName := s!"{fname}_applied_to_{aname}"
        let alreadyTried := concepts.any (fun c => getConceptName c == proposedName)

        if !alreadyTried && fname != aname then
          let atype ← inferType avalue
          if ← isDefEq atype argType then
            try
              let resultValue := mkApp fvalue avalue
              if !resultValue.hasLooseBVars then
                let resultType ← inferType resultValue

                let newMeta := {
                  name := proposedName
                  created := 0
                  parent := some fname
                  interestingness := 0.7  -- Higher interest for seed function applications
                  useCount := 0
                  successCount := 0
                  specializationDepth := ameta.specializationDepth + 1
                  generationMethod := "application"
                }
                newConcepts := newConcepts ++ [
                  ConceptData.definition proposedName resultType resultValue none (fdeps ++ adeps ++ [aname]) newMeta
                ]
                applicationCount := applicationCount + 1
            catch _ => pure ()
    | _ => pure ()

  -- Strategy 2: Apply recently successful functions
  let recentSuccesses := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if !t.hasLooseBVars && !v.hasLooseBVars && m.successCount > 0 && t.isForall then
        some (n, t, v, d, m)
      else none
    | _ => none

  for (fname, ftype, fvalue, fdeps, fmeta) in recentSuccesses.take 3 do
    match ← whnf ftype with
    | .forallE _ argType _ _ =>
      for (aname, _, avalue, adeps, ameta) in allArgs.take 3 do
        let proposedName := s!"{fname}_to_{aname}_v2"
        if !concepts.any (fun c => getConceptName c == proposedName) && fname != aname then
          let atype ← inferType avalue
          if ← isDefEq atype argType then
            try
              let resultValue := mkApp fvalue avalue
              if !resultValue.hasLooseBVars then
                let resultType ← inferType resultValue
                let newMeta := {
                  name := proposedName
                  created := 0
                  parent := some fname
                  interestingness := 0.8  -- Higher for successful patterns
                  useCount := 0
                  successCount := 0
                  specializationDepth := max fmeta.specializationDepth ameta.specializationDepth + 1
                  generationMethod := "application"
                }
                newConcepts := newConcepts ++ [
                  ConceptData.definition proposedName resultType resultValue none (fdeps ++ adeps) newMeta
                ]
            catch _ => pure ()
    | _ => pure ()

  return newConcepts

/-- Compose existing concepts to create new ones -/
def compositionHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []

  -- Only look for Nat -> Nat functions
  let natFunctions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
        match t with
        | Expr.forallE _ (Expr.const ``Nat _) (Expr.const ``Nat _) _ =>
          if m.specializationDepth < 2 then
            some (n, v, d, m)
          else none
        | _ => none
    | _ => none

  debugPrint false s!"[DEBUG] compositionHeuristic: found {natFunctions.length} Nat->Nat functions"

  -- Compose pairs of Nat -> Nat functions
  for (f₁, v₁, d₁, m₁) in natFunctions do
    for (f₂, v₂, d₂, m₂) in natFunctions do
      if f₁ ≠ f₂ then
        let compName := s!"{f₁}_compose_{f₂}"
        unless concepts.any (fun c => getConceptName c = compName) do
          try
            debugPrint false s!"[DEBUG] Trying to compose {f₁} with {f₂}"
            -- For Nat -> Nat, composition is straightforward
            let natType := mkConst ``Nat
            let compType := mkForall `x BinderInfo.default natType natType

            -- Build λ x => f₁ (f₂ x)
            let compVal ← withLocalDecl `x BinderInfo.default natType fun x => do
              let f₂x := mkApp v₂ x
              let result := mkApp v₁ f₂x
              mkLambdaFVars #[x] result

            let compDef := ConceptData.definition compName compType compVal none (d₁ ++ d₂)
              { name := compName
                created := 0
                parent := some f₁
                interestingness := 0.7
                useCount := 0
                successCount := 0
                specializationDepth := max m₁.specializationDepth m₂.specializationDepth + 1
                generationMethod := "composition" }

            newConcepts := newConcepts ++ [compDef]
            debugPrint false s!"[DEBUG] Successfully composed {f₁} with {f₂}"
          catch e =>
            debugPrint false s!"[DEBUG] Failed to compose {f₁} with {f₂}"

  debugPrint false s!"[DEBUG] compositionHeuristic: returning {newConcepts.length} concepts"
  return newConcepts

/-- Goal-directed concept generation heuristic - generates concepts to help prove specific goals -/
def goalDirectedHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Extract proof context (this would come from HeuristicContext in full implementation)
  let highEvidenceConjectures := concepts.filterMap fun c => match c with
    | ConceptData.conjecture name statement evidence meta =>
      if evidence > 0.7 then some (name, statement, evidence, meta) else none
    | _ => none
  
  IO.println s!"[GOAL-DIRECTED] Found {highEvidenceConjectures.length} high-evidence conjectures to target"
  
  for (conjName, conjStatement, evidence, conjMeta) in highEvidenceConjectures.take 5 do
    IO.println s!"[GOAL-DIRECTED] Targeting conjecture: {conjName}"
    
    -- Strategy 1: Generate supporting lemmas for the conjecture
    let lemmaName := s!"lemma_for_{conjName}"
    if !concepts.any (fun c => getConceptName c == lemmaName) then
      -- Create a supporting lemma conjecture (simplified approach)
      newConcepts := newConcepts ++ [
        ConceptData.conjecture lemmaName conjStatement (evidence * 0.9) {
          name := lemmaName
          created := 0
          parent := some conjName
          interestingness := evidence * 0.95
          useCount := 0
          successCount := 0
          specializationDepth := conjMeta.specializationDepth + 1
          generationMethod := "goal_directed_lemma"
        }
      ]
    
    -- Strategy 2: Generate intermediate steps by analyzing the statement structure
    match conjStatement with
    | Expr.forallE varName varType body _ =>
      -- For universal statements, try to create specialized instances
      let specializedName := s!"{conjName}_specialized"
      if !concepts.any (fun c => getConceptName c == specializedName) then
        -- Look for suitable terms to instantiate with
        let suitableTerms := concepts.filterMap fun c => match c with
          | ConceptData.definition name typ _ _ _ meta =>
            if meta.generationMethod == "seed" || meta.generationMethod == "mined" then
              -- Basic type checking - this is simplified
              if toString typ == toString varType then some name else none
            else none
          | _ => none
        
        for termName in suitableTerms.take 3 do
          let specName := s!"{conjName}_spec_{termName}"
          if !concepts.any (fun c => getConceptName c == specName) then
            newConcepts := newConcepts ++ [
              ConceptData.conjecture specName body (evidence * 0.8) {
                name := specName
                created := 0
                parent := some conjName
                interestingness := evidence * 0.85
                useCount := 0
                successCount := 0
                specializationDepth := conjMeta.specializationDepth + 1
                generationMethod := "goal_directed_specialization"
              }
            ]
    | _ => pure ()
    
    -- Strategy 3: Generate inverse or dual concepts
    let inverseName := s!"inverse_{conjName}"
    if !concepts.any (fun c => getConceptName c == inverseName) then
      newConcepts := newConcepts ++ [
        ConceptData.conjecture inverseName conjStatement (evidence * 0.7) {
          name := inverseName
          created := 0
          parent := some conjName
          interestingness := evidence * 0.8
          useCount := 0
          successCount := 0
          specializationDepth := conjMeta.specializationDepth + 1
          generationMethod := "goal_directed_inverse"
        }
      ]
  
  -- Strategy 4: Generate concepts to fill gaps identified in failed proofs
  let failedProofPatterns := concepts.filterMap fun c => match c with
    | ConceptData.conjecture name _ evidence meta =>
      if evidence < 0.3 && meta.useCount > 2 then some name else none
    | _ => none
  
  for failedName in failedProofPatterns.take 3 do
    let bridgeName := s!"bridge_to_{failedName}"
    if !concepts.any (fun c => getConceptName c == bridgeName) then
      -- Create a bridging concept that might help prove the failed conjecture
      newConcepts := newConcepts ++ [
        ConceptData.definition bridgeName (Expr.sort Level.zero) (mkConst ``True) none [failedName] {
          name := bridgeName
          created := 0
          parent := some failedName
          interestingness := 0.6
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "goal_directed_bridge"
        }
      ]
  
  IO.println s!"[GOAL-DIRECTED] Generated {newConcepts.length} goal-directed concepts"
  return newConcepts

/-- Backwards reasoning heuristic - generates concepts needed to prove target theorems -/
def backwardsReasoningHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find theorems that might need intermediate steps
  let targetTheorems := concepts.filterMap fun c => match c with
    | ConceptData.theorem name statement _ deps meta =>
      if meta.specializationDepth <= 1 && deps.length > 1 then
        some (name, statement, deps, meta)
      else none
    | _ => none
  
  IO.println s!"[BACKWARDS] Analyzing {targetTheorems.length} target theorems for backwards reasoning"
  
  for (thmName, statement, deps, meta) in targetTheorems.take 3 do
    IO.println s!"[BACKWARDS] Working backwards from theorem: {thmName}"
    
    -- Strategy 1: Generate missing intermediate theorems
    for dep in deps do
      let intermediateName := s!"intermediate_for_{thmName}_via_{dep}"
      if !concepts.any (fun c => getConceptName c == intermediateName) then
        -- Create an intermediate theorem conjecture
        newConcepts := newConcepts ++ [
          ConceptData.conjecture intermediateName statement 0.8 {
            name := intermediateName
            created := 0
            parent := some thmName
            interestingness := 0.85
            useCount := 0
            successCount := 0
            specializationDepth := meta.specializationDepth + 1
            generationMethod := "backwards_reasoning_intermediate"
          }
        ]
    
    -- Strategy 2: Generate helper lemmas by analyzing statement structure
    match statement with
    | Expr.forallE _ _ body _ =>
      -- For implications or universal statements, generate the antecedent as a lemma
      let antecedentName := s!"antecedent_for_{thmName}"
      if !concepts.any (fun c => getConceptName c == antecedentName) then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture antecedentName body 0.7 {
            name := antecedentName
            created := 0
            parent := some thmName
            interestingness := 0.8
            useCount := 0
            successCount := 0
            specializationDepth := meta.specializationDepth + 1
            generationMethod := "backwards_reasoning_antecedent"
          }
        ]
    | Expr.app f arg =>
      -- For applications, generate lemmas about the function and argument
      let functionLemmaName := s!"function_lemma_for_{thmName}"
      if !concepts.any (fun c => getConceptName c == functionLemmaName) then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture functionLemmaName f 0.6 {
            name := functionLemmaName
            created := 0
            parent := some thmName
            interestingness := 0.75
            useCount := 0
            successCount := 0
            specializationDepth := meta.specializationDepth + 1
            generationMethod := "backwards_reasoning_function"
          }
        ]
    | _ => pure ()
    
    -- Strategy 3: Generate dual or contrapositive statements
    let dualName := s!"dual_of_{thmName}"
    if !concepts.any (fun c => getConceptName c == dualName) then
      newConcepts := newConcepts ++ [
        ConceptData.conjecture dualName statement 0.6 {
          name := dualName
          created := 0
          parent := some thmName
          interestingness := 0.7
          useCount := 0
          successCount := 0
          specializationDepth := meta.specializationDepth + 1
          generationMethod := "backwards_reasoning_dual"
        }
      ]
  
  -- Strategy 4: Generate prerequisite concepts for failed proofs
  let failedConjectures := concepts.filterMap fun c => match c with
    | ConceptData.conjecture name _ evidence meta =>
      if evidence < 0.4 && meta.useCount > 1 then some (name, meta) else none
    | _ => none
  
  for (failedName, failedMeta) in failedConjectures.take 2 do
    let prereqName := s!"prerequisite_for_{failedName}"
    if !concepts.any (fun c => getConceptName c == prereqName) then
      newConcepts := newConcepts ++ [
        ConceptData.definition prereqName (Expr.sort Level.zero) (mkConst ``True) none [failedName] {
          name := prereqName
          created := 0
          parent := some failedName
          interestingness := 0.65
          useCount := 0
          successCount := 0
          specializationDepth := failedMeta.specializationDepth + 1
          generationMethod := "backwards_reasoning_prerequisite"
        }
      ]
  
  IO.println s!"[BACKWARDS] Generated {newConcepts.length} backwards reasoning concepts"
  return newConcepts

/-- Stochastic exploration heuristic - creates random variations to break cycles -/
def stochasticExplorationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Get a pseudo-random seed based on the number of concepts
  let seed := concepts.length % 17 + 3
  
  -- Find diverse concepts to experiment with
  let experimentCandidates := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      n.length % 5 == seed % 5 && m.specializationDepth <= 2 && m.generationMethod != "stochastic_exploration"
    | ConceptData.theorem n _ _ _ m => 
      n.length % 7 == (seed + 2) % 7 && m.specializationDepth <= 1
    | _ => false
  
  IO.println s!"[STOCHASTIC] Found {experimentCandidates.length} exploration candidates"
  
  -- Create random variations
  for candidate in experimentCandidates.take 3 do
    let baseName := getConceptName candidate
    let meta := getConceptMetadata candidate
    
    -- Create a "twisted" version with different naming
    let twistedName := s!"twist_{seed}_{baseName}"
    
    if !concepts.any (fun c => getConceptName c == twistedName) then
      match candidate with
      | ConceptData.definition _ t v cv deps _ =>
        let newMeta := { meta with
          name := twistedName
          parent := some baseName
          interestingness := 0.6 + (seed % 4).toFloat / 10.0  -- Slight randomness
          specializationDepth := meta.specializationDepth + 1
          generationMethod := "stochastic_exploration" }
        
        newConcepts := newConcepts ++ [
          ConceptData.definition twistedName t v cv deps newMeta
        ]
        
      | ConceptData.theorem _ s p deps _ =>
        let newMeta := { meta with
          name := twistedName
          parent := some baseName
          interestingness := 0.7 + (seed % 3).toFloat / 10.0
          specializationDepth := meta.specializationDepth + 1
          generationMethod := "stochastic_exploration" }
        
        newConcepts := newConcepts ++ [
          ConceptData.theorem twistedName s p deps newMeta
        ]
      | _ => pure ()
  
  -- Create some "bridging" concepts that connect distant concepts
  let definitions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ _ m => 
      if m.specializationDepth == 0 && n.length % 4 == (seed + 1) % 4 then
        some (n, t, v)
      else none
    | _ => none
  
  if definitions.length >= 2 then
    let (n1, t1, v1) := definitions[0]!
    let (n2, t2, v2) := definitions[1]!
    
    let bridgeName := s!"bridge_{n1}_{n2}"
    
    if !concepts.any (fun c => getConceptName c == bridgeName) then
      -- Create a simple bridging concept (placeholder - uses first concept's structure)
      newConcepts := newConcepts ++ [
        ConceptData.definition bridgeName t1 v1 none [n1, n2] {
          name := bridgeName
          created := 0
          parent := some n1
          interestingness := 0.65
          useCount := 0
          successCount := 0
          specializationDepth := 1
          generationMethod := "stochastic_bridging"
        }
      ]
  
  IO.println s!"[STOCHASTIC] Generated {newConcepts.length} exploration concepts"
  return newConcepts

/-- Cross-iteration synthesis heuristic: connects discoveries across different iteration layers -/
def crossIterationSynthesisHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Strategy 1: Identify underexplored successful patterns
  let successfulConcepts := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      m.successCount > 0 && m.useCount < 5
    | ConceptData.theorem n _ _ _ m =>
      m.successCount > 0 && m.useCount < 3  
    | _ => false
    
  let foundationalConcepts := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      m.generationMethod == "seed" || m.generationMethod == "mined"
    | _ => false
    
  -- Strategy 2: Cross-apply successful patterns to foundational concepts
  for successfulConcept in successfulConcepts.take 5 do
    for foundationalConcept in foundationalConcepts.take 5 do
      let successName := getConceptName successfulConcept
      let foundName := getConceptName foundationalConcept
      let synthName := s!"cross_apply_{successName}_to_{foundName}"
      
      if !concepts.any (fun c => getConceptName c == synthName) then
        -- Create a conjecture about applying the successful pattern
        let baseInterest := (getConceptMetadata successfulConcept).interestingness
        newConcepts := newConcepts ++ [
          ConceptData.conjecture synthName
            (mkConst ``True)  -- Placeholder statement
            (baseInterest * 0.8)
            { name := synthName
              created := 0
              parent := some successName
              interestingness := baseInterest * 0.8
              useCount := 0
              successCount := 0
              specializationDepth := 1
              generationMethod := "cross_iteration_synthesis" }
        ]
  
  -- Strategy 3: Explore variations of recently proven theorems
  let recentTheorems := concepts.filter fun c => match c with
    | ConceptData.theorem n _ _ _ m =>
      m.generationMethod != "mined" && m.specializationDepth <= 1
    | _ => false
    
  for thm in recentTheorems.take 3 do
    let thmName := getConceptName thm
    let variationName := s!"variation_{thmName}"
    
    if !concepts.any (fun c => getConceptName c == variationName) then
      newConcepts := newConcepts ++ [
        ConceptData.pattern variationName
          s!"Variation pattern based on theorem {thmName}"
          [thmName]
          { name := variationName
            created := 0
            parent := some thmName
            interestingness := 0.7
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "cross_iteration_synthesis" }
      ]
      
  -- Strategy 4: Create meta-patterns about discovery methods
  let methodCounts := ["application", "composition", "specialization", "conjecture"].map fun method =>
    let count := concepts.filter (fun c => (getConceptMetadata c).generationMethod == method) |>.length
    (method, count)
    
  for (method, count) in methodCounts do
    if count > 5 then
      let metaPatternName := s!"meta_pattern_{method}_successful"
      if !concepts.any (fun c => getConceptName c == metaPatternName) then
        newConcepts := newConcepts ++ [
          ConceptData.pattern metaPatternName
            s!"Meta-pattern: {method} has been successful ({count} concepts)"
            [s!"{method}_examples"]
            { name := metaPatternName
              created := 0
              parent := none
              interestingness := 0.8
              useCount := 0
              successCount := 0
              specializationDepth := 0
              generationMethod := "meta_pattern_recognition" }
        ]
        
  IO.println s!"[CROSS-ITER] Generated {newConcepts.length} synthesis concepts (successful: {successfulConcepts.length}, foundational: {foundationalConcepts.length}, recent theorems: {recentTheorems.length})"
  return newConcepts

/-- Historical memory heuristic: Uses full discovery history to find missed opportunities -/
def historicalMemoryHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Find concepts that have been mentioned as dependencies but not fully explored
  let allDependencies := concepts.foldl (fun acc c => match c with
    | ConceptData.definition _ _ _ _ deps _ => acc ++ deps
    | ConceptData.theorem _ _ _ deps _ => acc ++ deps
    | _ => acc
  ) []
  
  let actualConcepts := concepts.map getConceptName
  let missingDependencies := allDependencies.filter (fun dep => !actualConcepts.contains dep)
  
  IO.println s!"[MEMORY] Found {missingDependencies.length} missing dependencies to explore"
  
  -- Create placeholder concepts for missing dependencies
  for missingDep in missingDependencies.take 5 do
    let placeholderName := s!"inferred_{missingDep}"
    if !concepts.any (fun c => getConceptName c == placeholderName) then
      newConcepts := newConcepts ++ [
        ConceptData.pattern placeholderName
          s!"Inferred concept based on dependency analysis: {missingDep}"
          [missingDep]
          { name := placeholderName
            created := 0
            parent := none
            interestingness := 0.6
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "historical_memory" }
      ]
  
  -- Find underutilized successful concepts and try to build on them
  let underutilizedSuccesses := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      m.successCount > 0 && m.useCount == 0 && m.generationMethod != "number_generation"
    | ConceptData.theorem n _ _ _ m =>
      m.successCount > 0 && m.useCount == 0
    | _ => false
    
  for underutilized in underutilizedSuccesses.take 3 do
    let baseName := getConceptName underutilized
    let extensionName := s!"extension_{baseName}"
    
    if !concepts.any (fun c => getConceptName c == extensionName) then
      newConcepts := newConcepts ++ [
        ConceptData.conjecture extensionName
          (mkConst ``True)  -- Placeholder
          0.75
          { name := extensionName
            created := 0
            parent := some baseName
            interestingness := 0.75
            useCount := 0
            successCount := 0
            specializationDepth := 1
            generationMethod := "historical_memory" }
      ]
  
  IO.println s!"[MEMORY] Generated {newConcepts.length} memory-guided concepts"
  return newConcepts

/-- Concept freshness heuristic: Creates variations to combat convergence -/
def conceptFreshnessHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts : List ConceptData := []
  
  -- Strategy 1: Create semantic variations of successful definitions
  let successfulDefs := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      m.successCount > 0 && m.generationMethod != "number_generation" && !n.startsWith "variation_"
    | _ => false
    
  for defConcept in successfulDefs.take 3 do
    let baseName := getConceptName defConcept
    let variations := [s!"alt_{baseName}", s!"enhanced_{baseName}", s!"refined_{baseName}"]
    
    for varName in variations do
      if !concepts.any (fun c => getConceptName c == varName) then
        match defConcept with
        | ConceptData.definition _ defType defValue _ deps meta =>
          newConcepts := newConcepts ++ [
            ConceptData.definition varName defType defValue none deps
              { meta with 
                name := varName
                parent := some baseName
                interestingness := meta.interestingness * 0.9
                specializationDepth := meta.specializationDepth + 1
                generationMethod := "freshness_variation" }
          ]
        | _ => pure ()
        
  -- Strategy 2: Create conceptual bridges between distant concepts
  let earlySuccesses := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      m.generationMethod == "seed" && m.successCount > 0
    | _ => false
      
  let recentSuccesses := concepts.filter fun c => match c with
    | ConceptData.definition n _ _ _ _ m => 
      m.successCount > 0 && m.specializationDepth > 0
    | _ => false
    
  for early in earlySuccesses.take 2 do
    for recent in recentSuccesses.take 2 do
      let earlyName := getConceptName early
      let recentName := getConceptName recent
      let bridgeName := s!"bridge_{earlyName}_{recentName}_v2"
      
      if !concepts.any (fun c => getConceptName c == bridgeName) then
        newConcepts := newConcepts ++ [
          ConceptData.conjecture bridgeName
            (mkConst ``True)  -- Placeholder
            0.6
            { name := bridgeName
              created := 0
              parent := some earlyName
              interestingness := 0.6
              useCount := 0
              successCount := 0
              specializationDepth := 1
              generationMethod := "freshness_bridge" }
        ]
        
  -- Strategy 3: Revive abandoned patterns with new names
  let abandonedPatterns := concepts.filter fun c => match c with
    | ConceptData.pattern n _ _ m => 
      m.useCount == 0 && !n.startsWith "revived_"
    | _ => false
    
  for pattern in abandonedPatterns.take 2 do
    let patternName := getConceptName pattern
    let revivedName := s!"revived_{patternName}"
    
    if !concepts.any (fun c => getConceptName c == revivedName) then
      match pattern with
      | ConceptData.pattern _ desc instances meta =>
        newConcepts := newConcepts ++ [
          ConceptData.pattern revivedName
            s!"Revived: {desc}"
            instances
            { meta with
              name := revivedName
              parent := some patternName
              interestingness := 0.7
              useCount := 0
              generationMethod := "freshness_revival" }
        ]
      | _ => pure ()
      
  IO.println s!"[FRESHNESS] Generated {newConcepts.length} freshness concepts (successful defs: {successfulDefs.length}, early: {earlySuccesses.length}, recent: {recentSuccesses.length}, abandoned: {abandonedPatterns.length})"
  return newConcepts

/-- Complexity evaluation task -/
def complexityTask : EvaluationFn := fun concepts => do
  if let some concept := concepts.getLast? then
    match concept with
    | ConceptData.definition _ t v _ _ meta =>
      -- Measure expression complexity
      let typeSize := (exprSize t).toFloat
      let valueSize := (exprSize v).toFloat
      let depthPenalty := meta.specializationDepth.toFloat * 0.1
      let complexity := typeSize + valueSize + depthPenalty * 10.0
      -- Prefer simpler concepts
      return 1.0 / (1.0 + complexity / 10.0)
    | ConceptData.theorem _ s p _ meta =>
      let stmtSize := (exprSize s).toFloat
      let proofSize := (exprSize p).toFloat
      let depthPenalty := meta.specializationDepth.toFloat * 0.1
      let complexity := stmtSize + proofSize / 2.0 + depthPenalty * 10.0
      return 1.0 / (1.0 + complexity / 20.0)
    | ConceptData.conjecture _ _ evidence _ =>
      -- Conjectures are interesting based on evidence
      return evidence
    | ConceptData.pattern _ _ instances _ =>
      -- Patterns are interesting based on number of instances
      return min 1.0 (instances.length.toFloat / 5.0)
    | _ => return 0.5
  else
    return 0.5

/-- Novelty evaluation task -/
def noveltyTask : EvaluationFn := fun concepts => do
  if let some newConcept := concepts.getLast? then
    let name := getConceptName newConcept
    let meta := getConceptMetadata newConcept

    -- Bonus for conjectures and patterns
    let typeBonus := match newConcept with
      | ConceptData.conjecture _ _ _ _ => 0.2
      | ConceptData.pattern _ _ _ _ => 0.3
      | _ => 0.0

    -- Penalize deep specializations
    let depthPenalty := meta.specializationDepth.toFloat * 0.2

    -- Check how different the name is from existing concepts
    let mut maxSimilarity := 0.0
    for c in concepts.dropLast do
      let existingName := getConceptName c
      -- Simple similarity: count common characters
      let commonChars := name.toList.filter (existingName.toList.contains ·) |>.length
      let similarity := commonChars.toFloat / (max name.length existingName.length).toFloat
      maxSimilarity := max maxSimilarity similarity

    -- Return novelty score
    return max 0.1 (1.0 - maxSimilarity * 0.5 - depthPenalty + typeBonus)
  else
    return 0.5

/-- Pattern importance evaluation task -/
def patternImportanceTask : EvaluationFn := fun concepts => do
  if let some concept := concepts.getLast? then
    match concept with
    | ConceptData.pattern _ _ instances _ =>
      -- Patterns with more instances are more important
      let instanceBonus := instances.length.toFloat / 10.0
      -- Patterns that connect different concept types are valuable
      let mut diversityScore := 0.0
      let mut hasNumbers := false
      let mut hasApplications := false
      for inst in instances do
        if inst.startsWith "num_" || inst == "zero" || inst == "one" then
          hasNumbers := true
        if (inst.splitOn "_applied_to_").length > 1 then
          hasApplications := true
      if hasNumbers && hasApplications then
        diversityScore := 0.3

      return min 1.0 (0.5 + instanceBonus + diversityScore)
    | _ =>
      -- Use default complexity evaluation for non-patterns
      complexityTask concepts
  else
    return 0.5

/-- Initialize system with seed concepts and heuristics -/
def initializeSystem (config : DiscoveryConfig) (useMining : Bool := true) : MetaM KnowledgeBase := do
  let basicMeta : ConceptMetadata := {
    name := "initial"
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := "initial"
  }

  -- Get seed concepts
  let mut initialConcepts ← seedConcepts

  -- Optionally add some mined concepts
  if useMining then
    let minedConcepts ← mineEnvironment ["Nat.zero", "Nat.succ", "Nat.add", "Nat.sub", "Nat.mul"] ["Mathlib.Algebra.Group", "Mathlib.Algebra.Ring"]
    -- Clean up mined concepts against existing
    let cleanedMined ← cleanupConcepts config initialConcepts minedConcepts 0
    initialConcepts := initialConcepts ++ cleanedMined.take 300

  -- Create heuristic references
  let specHeuristicRef := ConceptData.heuristicRef
    "specialization"
    "Create specific instances of universal theorems"
    { basicMeta with name := "specialization" }

  let appHeuristicRef := ConceptData.heuristicRef
    "application"
    "Apply functions to suitable arguments"
    { basicMeta with name := "application" }

  let lemmaAppHeuristicRef := ConceptData.heuristicRef
    "lemma_application"
    "Apply any mined Eq-theorem whose LHS matches another concept"
    { basicMeta with name := "lemma_application" }

  let patternHeuristicRef := ConceptData.heuristicRef
    "pattern_recognition"
    "Identify mathematical patterns in discovered concepts"
    { basicMeta with name := "pattern_recognition" }

  let conjectureHeuristicRef := ConceptData.heuristicRef
    "conjecture_generation"
    "Generate plausible mathematical conjectures"
    { basicMeta with name := "conjecture_generation" }

  let compositionHeuristicRef := ConceptData.heuristicRef
    "composition"
    "Compose functions to create new concepts"
    { basicMeta with name := "composition" }

  let patternGuidedHeuristicRef := ConceptData.heuristicRef
    "pattern_guided"
    "Use discovered patterns to guide generation"
    { basicMeta with name := "pattern_guided" }

  let goalDirectedHeuristicRef := ConceptData.heuristicRef
    "goal_directed"
    "Generate concepts to prove specific high-evidence conjectures"
    { basicMeta with name := "goal_directed" }

  let backwardsReasoningHeuristicRef := ConceptData.heuristicRef
    "backwards_reasoning"
    "Generate concepts needed to prove target theorems via backwards reasoning"
    { basicMeta with name := "backwards_reasoning" }

  let stochasticHeuristicRef := ConceptData.heuristicRef
    "stochastic_exploration"
    "Create random variations to break discovery cycles"
    { basicMeta with name := "stochastic_exploration" }

  let crossIterHeuristicRef := ConceptData.heuristicRef
    "cross_iteration_synthesis"
    "Connect discoveries across different iteration layers"
    { basicMeta with name := "cross_iteration_synthesis" }

  let historicalMemoryRef := ConceptData.heuristicRef
    "historical_memory"
    "Use full discovery history to find missed opportunities"
    { basicMeta with name := "historical_memory" }

  let conceptFreshnessRef := ConceptData.heuristicRef
    "concept_freshness"
    "Create variations to combat discovery convergence"
    { basicMeta with name := "concept_freshness" }

  -- Create task references
  let complexityTaskRef := ConceptData.taskRef
    "complexity"
    "Prefer simpler concepts"
    { basicMeta with name := "complexity" }

  let noveltyTaskRef := ConceptData.taskRef
    "novelty"
    "Prefer novel concepts"
    { basicMeta with name := "novelty" }

  let patternTaskRef := ConceptData.taskRef
    "pattern_importance"
    "Evaluate importance of discovered patterns"
    { basicMeta with name := "pattern_importance" }

  -- Build registries
  let mut heuristics : HeuristicRegistry := HeuristicRegistry.empty
  heuristics := heuristics.insert "specialization" specializationHeuristic
  heuristics := heuristics.insert "application" applicationHeuristic
  heuristics := heuristics.insert "lemma_application" lemmaApplicationHeuristic
  heuristics := heuristics.insert "pattern_recognition" patternRecognitionHeuristic
  heuristics := heuristics.insert "conjecture_generation" conjectureGenerationHeuristic
  heuristics := heuristics.insert "composition" compositionHeuristic
  heuristics := heuristics.insert "pattern_guided" patternGuidedHeuristic
  heuristics := heuristics.insert "goal_directed" goalDirectedHeuristic
  heuristics := heuristics.insert "backwards_reasoning" backwardsReasoningHeuristic
  heuristics := heuristics.insert "stochastic_exploration" stochasticExplorationHeuristic
  heuristics := heuristics.insert "cross_iteration_synthesis" crossIterationSynthesisHeuristic
  heuristics := heuristics.insert "historical_memory" historicalMemoryHeuristic
  heuristics := heuristics.insert "concept_freshness" conceptFreshnessHeuristic

  let mut evaluators : EvaluationRegistry := EvaluationRegistry.empty
  evaluators := evaluators.insert "complexity" complexityTask
  evaluators := evaluators.insert "novelty" noveltyTask
  evaluators := evaluators.insert "pattern_importance" patternImportanceTask

  let allConcepts := initialConcepts ++ [
      specHeuristicRef, appHeuristicRef, lemmaAppHeuristicRef,
      patternHeuristicRef, conjectureHeuristicRef, compositionHeuristicRef,
      patternGuidedHeuristicRef, goalDirectedHeuristicRef, backwardsReasoningHeuristicRef,
      stochasticHeuristicRef, crossIterHeuristicRef, historicalMemoryRef, conceptFreshnessRef,
      complexityTaskRef, noveltyTaskRef, patternTaskRef
    ]
  
  -- Initialize concept layers with foundational concepts
  let initialLayers : ConceptLayers := {
    foundational := allConcepts
    historical := []
    recent := allConcepts
    current := []
  }
  
  return {
    concepts := allConcepts
    layers := initialLayers
    recentConcepts := allConcepts
    heuristics := heuristics
    evaluators := evaluators
    config := config
    iteration := 0
    history := []
    cache := {}
    failedProofs := []
  }

/-- Update concept layers for next iteration -/
def updateConceptLayers (layers : ConceptLayers) (newConcepts : List ConceptData) (iteration : Nat) : ConceptLayers :=
  if iteration <= 2 then
    -- Early iterations: build foundational layer
    { foundational := layers.foundational ++ newConcepts
      historical := layers.historical
      recent := layers.recent ++ newConcepts  
      current := newConcepts }
  else
    -- Later iterations: age concepts through layers
    { foundational := layers.foundational
      historical := layers.historical ++ layers.recent
      recent := layers.current ++ newConcepts
      current := newConcepts }

/-- Get all concepts from layers in priority order -/
def getAllFromLayers (layers : ConceptLayers) : List ConceptData :=
  layers.foundational ++ layers.historical ++ layers.recent ++ layers.current

/-- Get concept interestingness -/
def getInterestingness (c : ConceptData) : Float :=
  (getConceptMetadata c).interestingness

/-- Show concept statistics -/
def showConceptStats (concepts : List ConceptData) : IO Unit := do
  let defs := concepts.filter fun c => match c with
    | ConceptData.definition _ _ _ _ _ _ => true
    | _ => false
  let thms := concepts.filter fun c => match c with
    | ConceptData.theorem _ _ _ _ _ => true
    | _ => false
  let conjs := concepts.filter fun c => match c with
    | ConceptData.conjecture _ _ _ _ => true
    | _ => false
  let patterns := concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true
    | _ => false

  -- Build depth histogram manually
  let mut depthCounts : List (Nat × Nat) := []
  for c in concepts do
    let depth := (getConceptMetadata c).specializationDepth
    match depthCounts.find? (·.1 == depth) with
    | some (_, count) =>
      depthCounts := depthCounts.filter (·.1 != depth) ++ [(depth, count + 1)]
    | none =>
      depthCounts := depthCounts ++ [(depth, 1)]

  IO.println s!"\nDefinitions: {defs.length}"
  IO.println s!"Theorems: {thms.length}"
  IO.println s!"Conjectures: {conjs.length}"
  IO.println s!"Patterns: {patterns.length}"
  IO.println s!"\nDepth distribution:"
  let sorted := depthCounts.toArray.qsort (·.1 < ·.1)
  for (depth, count) in sorted do
    IO.println s!"  Depth {depth}: {count} concepts"

/-- Run the discovery system -/
def runDiscoveryCustom
  (description : String)
  (initialConcepts : List ConceptData)
  (customHeuristics : List (String × HeuristicFn))
  (customEvaluators : List (String × EvaluationFn))
  (maxIterations : Nat := 10) (useMining : Bool := false) (config : DiscoveryConfig := {}) : MetaM Unit := do
  IO.println s!"=== Starting {description}Discovery System ==="
  IO.println s!"Config: maxDepth={config.maxSpecializationDepth}, maxPerIter={config.maxConceptsPerIteration}"
  IO.println s!"Features: conjectures={config.enableConjectures}, patterns={config.enablePatternRecognition}"
  IO.println s!"Mining mode: {if useMining then "ON" else "OFF"}"
  IO.println "Initializing with mathematical seed concepts..."

  let kb0 ← initializeSystem config useMining

  -- Build heuristics registry
  let mut heuristics : HeuristicRegistry := kb0.heuristics

  -- Add all heuristics (custom ones override standard if same name)
  for (name, fn) in customHeuristics do
    heuristics := heuristics.insert name fn

  -- Build evaluators registry
  let mut evaluators : EvaluationRegistry := kb0.evaluators

  -- Add all evaluators (custom ones override standard if same name)
  for (name, fn) in customEvaluators do
    evaluators := evaluators.insert name fn

  -- Create heuristic reference concepts
  let heuristicRefs := customHeuristics.map fun (name, _) =>
    ConceptData.heuristicRef name s!"Custom heuristic: {name}"
      { name := name
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "initial" }

  -- Create knowledge base
  let kb : KnowledgeBase := {
    concepts := initialConcepts ++ kb0.concepts ++ heuristicRefs
    recentConcepts := initialConcepts ++ kb0.concepts
    heuristics := heuristics
    evaluators := evaluators
    config := kb0.config
    iteration := kb0.iteration
    history := kb0.history
    cache := kb0.cache
    failedProofs := kb0.failedProofs
  }

  IO.println s!"\nInitial concepts ({kb.concepts.length}):"
  showConceptStats kb.concepts

  let finalKb ← discoveryLoop kb maxIterations

  IO.println s!"\n=== Discovery Complete ==="
  IO.println s!"Total concepts: {finalKb.concepts.length}"
  showConceptStats finalKb.concepts

  -- Show discovered patterns
  let patterns := finalKb.concepts.filter fun c => match c with
    | ConceptData.pattern _ _ _ _ => true
    | _ => false

  if patterns.length > 0 then
    IO.println s!"\nDiscovered Patterns:"
    for p in patterns do
      match p with
      | ConceptData.pattern name desc instances _ =>
        IO.println s!"  - {name}: {desc}"
        IO.println s!"    Instances: {instances}"
      | _ => pure ()

  -- Show top concepts
  let sorted := finalKb.concepts.toArray.qsort fun c1 c2 =>
    getInterestingness c1 > getInterestingness c2

  IO.println s!"\nTop discovered concepts:"
  for i in [:min 20 sorted.size] do
    if h : i < sorted.size then
      let c := sorted[i]
      let meta := getConceptMetadata c
      match c with
      | ConceptData.conjecture name _ evidence _ =>
        IO.println s!"  {name} (CONJECTURE, evidence: {evidence}, score: {(getInterestingness c).toString})"
      | ConceptData.pattern name _ _ _ =>
        IO.println s!"  {name} (PATTERN, score: {(getInterestingness c).toString})"
      | _ =>
        IO.println s!"  {getConceptName c} (score: {(getInterestingness c).toString}, depth: {meta.specializationDepth})"

def runDiscovery
  (maxIterations : Nat := 10) (useMining : Bool := false) (config : DiscoveryConfig := {}) : MetaM Unit := do
  runDiscoveryCustom "Lean" [] [] [] maxIterations useMining config

end LeanDisco
