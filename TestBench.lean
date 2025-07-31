import LeanDisco
import MiniF2F.Valid
import Lean

open Lean Meta Elab Tactic

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

-- Check if a theorem has a complete proof (no sorry, no metavariables)
def hasCompleteProof (info : ConstantInfo) : MetaM Bool := do
  match info with
  | .thmInfo thmInfo =>
    -- Check if the proof value depends on sorryAx
    let axioms := thmInfo.value.getUsedConstants
    if axioms.contains ``sorryAx then
      return false
    -- Also check for unassigned metavariables
    let hasMVars := thmInfo.value.hasExprMVar
    return !hasMVars
  | _ => return false

-- Extract all MiniF2F theorems using metaprogramming
def extractMiniF2FTheorems : MetaM (List (Name × ConstantInfo)) := do
  let env ← getEnv
  let allDecls := env.constants.toList
  let miniF2FDecls := allDecls.filter fun (name, info) =>
    -- Look for declarations that are theorems and match MiniF2F naming patterns
    match info with
    | .thmInfo _ =>
      let nameStr := name.toString
      -- Check if it's from MiniF2F by looking at naming patterns
      nameStr.startsWith "amc" || nameStr.startsWith "mathd" || nameStr.startsWith "aime" ||
      nameStr.startsWith "imo" || nameStr.startsWith "usamo" || nameStr.startsWith "induction"
    | _ => false
  return miniF2FDecls

-- Analyze and print theorem information
def analyzeTheorem (name : Name) (info : ConstantInfo) : MetaM Unit := do
  match info with
  | .thmInfo thmInfo => do
    IO.println s!"Theorem: {name}"
    IO.println s!"Type: {thmInfo.type}"

    -- Check if the proof is complete
    let isComplete ← hasCompleteProof info
    if isComplete then
      IO.println "Status: Has complete proof"
    else
      IO.println "Status: Incomplete proof"
    IO.println "---"
  | _ => pure ()

-- Main analysis function
def runMiniF2FAnalysis : MetaM Unit := do
  IO.println "MiniF2F Benchmark Analysis:"
  IO.println "=========================="

  let theorems ← extractMiniF2FTheorems
  IO.println s!"Found {theorems.length} theorems"

  -- Count theorems with complete proofs
  let mut completeProofs := 0
  let mut incompleteProofs := 0

  for (_, info) in theorems do
    let isComplete ← hasCompleteProof info
    if isComplete then
      completeProofs := completeProofs + 1
    else
      incompleteProofs := incompleteProofs + 1

  -- Calculate percentage
  let percentage := (completeProofs.toFloat / theorems.length.toFloat) * 100

  IO.println s!"\nSummary:"
  IO.println s!"- Complete proofs: {completeProofs} ({percentage.round}%)"
  IO.println s!"- Incomplete proofs: {incompleteProofs} ({(100.0 - percentage).round}%)"
  --IO.println "\nDetailed theorem list:\n"

  --for (name, info) in theorems do
  --  analyzeTheorem name info

def blacklistedTheorems := [
  "mathd_numbertheory_543"
]

-- Run prover on MiniF2F benchmark
def runProverAnalysis : TermElabM Unit := do
  IO.println "MiniF2F Automated Prover Analysis:"
  IO.println "=================================="

  let all_theorems ← extractMiniF2FTheorems
  let theorems := all_theorems.filter fun (name, _) => !blacklistedTheorems.contains name.toString

  let mut count := 0
  let mut proved := 0

  for (name, info) in theorems do
    match info with
    | .thmInfo thmInfo =>
      count := count + 1
      let result ← attemptProof thmInfo.type
      if result.isSome then
        proved := proved + 1
        --IO.println s!"✓ PROVED {name} with {result.get!}"
    | _ => pure ()
  IO.println s!"\nProver Summary:"
  IO.println s!"- Total theorems: {count}"
  IO.println s!"- Proved: {proved}"
  IO.println s!"- Success rate: {(proved.toFloat / count.toFloat * 100).round}%"

#eval runMiniF2FAnalysis.run'
#eval runProverAnalysis.run'

def main : IO Unit := do
  IO.println "Analysis run complete."
