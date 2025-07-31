import Lean
import LeanDisco.Prover

open Lean Meta Elab Term

/-- Core representation of all mathematical objects in the discovery system -/
structure ConceptData where
  name    : Name
  type    : Expr
  proof?  : Option Expr
  isDef   : Bool
  isProp  : Bool
  origin? : Option String := none

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

/-- One discovery iteration: run all heuristics and apply deltas -/
def stepDiscovery (heuristics : List (DiscoveryState → MetaM DiscoveryStateDelta)) (cfg : DiscoveryConfig) (state : DiscoveryState): MetaM DiscoveryState := do
  let deltas ← heuristics.mapM (fun h => h state)
  let combined : DiscoveryStateDelta := {
    newConcepts := deltas.map (·.newConcepts) |>.foldl (· ++ ·) #[],
    removedConcepts := deltas.map (·.removedConcepts) |>.foldl (· ++ ·) #[]
  }
  if cfg.logWorkStats then
    logInfo m!"[iteration {state.iteration}] +{combined.newConcepts.size} −{combined.removedConcepts.size}"
  return {
    concepts := state.concepts.filter (fun c => !combined.removedConcepts.contains c.name) ++ combined.newConcepts,
    newConcepts := combined.newConcepts,
    iteration := state.iteration + 1
  }

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
  for _ in [1:cfg.maxIterations] do
    state ← stepDiscovery heuristics cfg state
  return state

def runDiscovery (cfg: DiscoveryConfig) (domain: DiscoveryDomain): MetaM DiscoveryState := runDiscoveryWith [heuristicProveUnproven cfg] cfg domain
