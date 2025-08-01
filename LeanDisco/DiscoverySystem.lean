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
  logWorkStats : Bool := true
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
  | some pf => return some { c with proof? := some pf }
  | none => return none

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
  if cfg.logWorkStats then
    logInfo m!"[iteration {state.iteration}] +{combined.newConcepts.size} −{combined.removedConcepts.size}"
  let newState := {
    concepts := state.concepts.filter (fun c => !combined.removedConcepts.contains c.name) ++ combined.newConcepts,
    newConcepts := combined.newConcepts,
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
