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
  generators : List (DiscoveryConfig → Array ConceptData → MetaM (Array ConceptData))

/-- Tracks evolving state of the discovery system -/
structure DiscoveryState where
  concepts : Array ConceptData
  iteration : Nat
  deriving Inhabited

/-- Attempt to prove and promote conjectures into theorems -/
def proveAndPromote (cfg : DiscoveryConfig) (c : ConceptData) : MetaM (Option ConceptData) := do
  if c.proof?.isSome then return some c -- already proven
  if !cfg.enableProofSearch then return none
  let proofOpt ← TermElabM.run' (attemptProof c.type)
  match proofOpt with
  | some pf => return some { c with proof? := some pf }
  | none => return none

/-- One discovery iteration: generate + try to prove -/
def stepDiscovery (cfg : DiscoveryConfig) (domain : DiscoveryDomain) (state : DiscoveryState) : MetaM DiscoveryState := do
  let mut newConcepts : Array ConceptData := #[]

  -- Run each domain-specific generator
  for gen in domain.generators do
    let output ← gen cfg state.concepts
    newConcepts := newConcepts ++ output

  if cfg.logWorkStats then
    logInfo m!"[iteration {state.iteration}] generated {newConcepts.size} conjectures"

  if cfg.logEachConjecture then
    for c in newConcepts do
      logInfo m!"[iteration {state.iteration}] {← c.summary}"

  let toAttempt := newConcepts
  let total := toAttempt.size
  let proven := (← toAttempt.filterMapM (fun c => proveAndPromote cfg c))

  if cfg.logProgress then
    logInfo m!"[iteration {state.iteration}] tried {total}, proved {proven.size}"

  return {
    concepts := state.concepts ++ proven ++ (toAttempt.filter (·.proof?.isNone)),
    iteration := state.iteration + 1
  }

/-- Top-level discovery driver -/
def runDiscovery (cfg : DiscoveryConfig) (domain : DiscoveryDomain) : MetaM DiscoveryState := do
  let seed ← domain.seed
  let firstProven ← seed.filterMapM (fun c => proveAndPromote cfg c)
  let remaining ← seed.filterM (fun c => return c.proof?.isNone)
  if cfg.logProgress then
    logInfo m!"[seed] tried {seed.size}, proved {firstProven.size}"
  let mut state : DiscoveryState := {
    concepts := firstProven ++ remaining,
    iteration := 1
  }
  for _ in [1:cfg.maxIterations] do
    state ← stepDiscovery cfg domain state
  return state
