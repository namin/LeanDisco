import LeanDisco
import MiniF2F.Valid
import Lean

open Lean Meta Elab Tactic

set_option maxRecDepth 1000
set_option maxHeartbeats 10000000

-- Attempt to prove using Aesop with limited search depth
def attemptAesopProof (name : Name) (type : Expr) : TermElabM Bool := do
  let mvar ← mkFreshExprMVar type
  let goal := mvar.mvarId!

  try
    -- Run aesop tactic with strict limits to avoid stack overflow
    let remainingGoals ← Tactic.run goal do
      evalTactic (← `(tactic| aesop (config := { maxRuleApplications := 100, maxRuleApplicationDepth := 20 })))

    if remainingGoals.isEmpty then
      IO.println s!"✓ PROVED by aesop: {name}"
      return true
  catch _ =>
    -- Aesop failed, try with intros
    try
      let remainingGoals ← Tactic.run goal do
        evalTactic (← `(tactic| intros; aesop (config := { maxRuleApplications := 100, maxRuleApplicationDepth := 20 })))

      if remainingGoals.isEmpty then
        IO.println s!"✓ PROVED by intros;aesop: {name}"
        return true
    catch _ => pure ()

  return false

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

-- Run Aesop prover on MiniF2F benchmark
def runAesopAnalysis : TermElabM Unit := do
  IO.println "MiniF2F Aesop Prover Analysis:"
  IO.println "=============================="

  let theorems ← extractMiniF2FTheorems

  let mut count := 0
  let mut proved := 0

  for (name, info) in theorems do
    match info with
    | .thmInfo thmInfo =>
      count := count + 1
      let isProved ← attemptAesopProof name thmInfo.type
      if isProved then
        proved := proved + 1
    | _ => pure ()
  IO.println s!"\nProver Summary:"
  IO.println s!"- Total theorems: {count}"
  IO.println s!"- Proved: {proved}"
  IO.println s!"- Success rate: {(proved.toFloat / count.toFloat * 100).round}%"

#eval! runAesopAnalysis.run'

def main : IO Unit := do
  IO.println "Analysis run complete."
