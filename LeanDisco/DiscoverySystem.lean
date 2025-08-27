import Lean
import LeanDisco.Prover

open Lean Meta Elab Term

/-- Core representation of all mathematical objects in the discovery system -/
structure ConceptData where
  name     : Name
  type     : Expr
  proof?   : Option Expr
  isDef    : Bool
  isProp   : Bool
  origin?  : Option String := none
  tags     : List String := []
  contexts : Array Expr := #[]

/-- Summarized string form for logging -/
def ConceptData.summary (c : ConceptData) : MetaM String := do
  let name := c.name.toString
  let prop := if c.isProp then "Prop" else "Type"
  let status := if c.proof?.isSome then "✔️" else "❓"
  return s!"{status} {name} : {prop}"

/-- Tracks evolving state of the discovery system -/
structure DiscoveryState where
  concepts : Array ConceptData
  newConcepts : Array ConceptData := #[]
  iteration : Nat
  deriving Inhabited

/-- Sanity check: Verify that a proof actually proves the claimed type -/
def sanityCheckProof (concept : ConceptData) (strictMode : Bool := false) : MetaM Bool := do
  match concept.proof? with
  | none =>
    -- No proof provided is fine
    return true
  | some proof =>
    try
      -- Check that the proof has the right type
      let proofType ← inferType proof
      if ← isDefEq proofType concept.type then
        if "verified" ∈ concept.tags || "proven" ∈ concept.tags then
          -- Check if it's a complete proof
          if proof.getUsedConstants.contains ``sorryAx then
            if strictMode then
              logError m!"❌ Strict mode: {concept.name} claims to be verified/proven but uses sorryAx"
              return false
            else
              logInfo m!"⚠️ Warning: {concept.name} claims to be verified/proven but uses sorryAx"
              return true
          else if proof.hasExprMVar then
            logError m!"❌ {concept.name} has unassigned metavariables in proof"
            return false
          else
            return true
        else
          return true
      else
        logError m!"❌ Sanity check failed for {concept.name}: proof type doesn't match claimed type"
        logError m!"  Expected type: {concept.type}"
        logError m!"  Proof has type: {proofType}"
        return false
    catch e =>
      logError m!"❌ Sanity check failed for {concept.name}: {e.toMessageData}"
      return false

/-- Validate all concepts in a discovery state -/
def validateDiscoveryState (state : DiscoveryState) (strictMode : Bool := false) : MetaM Bool := do
  let mut allValid := true
  for concept in state.concepts do
    let valid ← sanityCheckProof concept strictMode
    if !valid then
      allValid := false
  if allValid then
    logInfo m!"✅ All {state.concepts.size} concepts passed sanity check"
  else
    logError m!"❌ Some concepts failed sanity check"
  return allValid

/-- Delta produced by heuristics to modify the discovery state -/
structure DiscoveryStateDelta where
  newConcepts : Array ConceptData := #[]
  removedConcepts : Array Name := #[]

/-- Configuration for controlling the discovery process -/
structure DiscoveryConfig where
  maxIterations : Nat := 10
  maxConceptsPerIteration : Nat := 50
  enableProofSearch : Bool := true
  logProgress : Bool := true
  logEachConjecture : Bool := false
  logProofSuccess : Bool := false
  logProofFailure : Bool := false
  logWorkStats : Bool := true
  enableSanityCheck : Bool := true  -- Check that proofs typecheck
  strictSanityCheck : Bool := false  -- If true, reject sorryAx proofs marked as "verified"
  deriving Inhabited

/-- Domain-specific extensions: seed concepts and generation heuristics -/
class DiscoveryDomain where
  name : String
  seed : MetaM (Array ConceptData)

/-- Attempt to prove and promote conjectures into theorems -/
def proveAndPromote (cfg : DiscoveryConfig) (c : ConceptData) : MetaM (Option ConceptData) := do
  if c.proof?.isSome then return some c -- already proven
  if !cfg.enableProofSearch then return none
  let proofOpt ← TermElabM.run' (attemptProof c.type)
  match proofOpt with
  | some pf =>
      if cfg.logProofSuccess then
        logInfo m!"✅ Proved {c.name}: {c.type}"
      return some { c with proof? := some pf }
  | none =>
      if cfg.logProofFailure then
        logInfo m!"❌ Failed to prove {c.name}: {c.type}"
      return none

/-- A heuristic that attempts to prove unproven concepts -/
def heuristicProveUnproven (cfg : DiscoveryConfig) (state : DiscoveryState) : MetaM DiscoveryStateDelta := do
  let toTry := state.newConcepts.filter (·.proof?.isNone)
  let results ← toTry.mapM (proveAndPromote cfg)
  let newTheorems := results.filterMap id
  return {
    newConcepts := newTheorems
    removedConcepts := newTheorems.map (·.name)
  }

/-- Heuristic: verbose print of any new concepts with a particular tag -/
def heuristicLogTagged (tag : String): DiscoveryState → MetaM DiscoveryStateDelta := fun state => do
  for c in state.newConcepts do
    if tag ∈ c.tags then
      logInfo m!"[{tag}] tagged concept: {← c.summary}"
  return {}

/-- Helper to count tags per iteration -/
def logTagFrequencies (label : String) (concepts : Array ConceptData) : MetaM Unit := do
  let mut counts : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity 10
  for c in concepts do
    for tag in c.tags do
    let count := match counts.contains tag with
      | true => counts[tag]!
      | false => 0
    counts := counts.insert tag (count + 1)
  if counts.isEmpty then
    logInfo m!"[{label}] tags: (none)"
  else
    let summary := counts.toList.map (fun (t, n) => s!"{t}: {n}")|> String.intercalate ", "
    logInfo m!"[{label}] tags: {summary}"

/-- One discovery iteration: run all heuristics and apply deltas -/
def stepDiscovery (heuristics : List (DiscoveryState → MetaM DiscoveryStateDelta)) (cfg : DiscoveryConfig) (state : DiscoveryState): MetaM DiscoveryState := do
  let deltas ← heuristics.mapM (fun h => h state)
  let combined : DiscoveryStateDelta := {
    newConcepts := deltas.map (·.newConcepts) |>.foldl (· ++ ·) #[],
    removedConcepts := deltas.map (·.removedConcepts) |>.foldl (· ++ ·) #[]
  }

  -- Sanity check new concepts before adding them
  let mut validatedConcepts := #[]
  if cfg.enableSanityCheck then
    for concept in combined.newConcepts do
      if ← sanityCheckProof concept cfg.strictSanityCheck then
        validatedConcepts := validatedConcepts.push concept
      else
        logError m!"Dropping invalid concept: {concept.name}"
  else
    validatedConcepts := combined.newConcepts

  if cfg.logWorkStats then
    logInfo m!"[iteration {state.iteration}] +{validatedConcepts.size} −{combined.removedConcepts.size}"

  let newState := {
    concepts := state.concepts.filter (fun c => !combined.removedConcepts.contains c.name) ++ validatedConcepts,
    newConcepts := validatedConcepts,
    iteration := state.iteration + 1
  }
  logTagFrequencies s!"iteration {state.iteration + 1}" newState.concepts
  return newState

/-- Top-level discovery driver -/
def runDiscoveryWith (heuristics : List (DiscoveryState → MetaM DiscoveryStateDelta)) (cfg : DiscoveryConfig) (domain : DiscoveryDomain) : MetaM DiscoveryState := do
  let seed ← domain.seed
  if cfg.logProgress then
    logInfo m!"[seed] loaded {seed.size} concepts"
  let mut state : DiscoveryState := {
    concepts := seed,
    newConcepts := seed,
    iteration := 1
  }
  logTagFrequencies "seed" seed
  for _ in [1:cfg.maxIterations] do
    state ← stepDiscovery heuristics cfg state
  return state

def runDiscovery (cfg: DiscoveryConfig) (domain: DiscoveryDomain): MetaM DiscoveryState := runDiscoveryWith [heuristicProveUnproven cfg] cfg domain
