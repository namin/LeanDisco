import LeanDisco
import MiniF2F.Valid
import Lean
import Auto.Tactic

open Lean Meta Elab Tactic

set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000

-- Configure lean-auto for SMT solving
set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"
set_option auto.smt.timeout 2
set_option auto.native false

-- Attempt to prove using auto with SMT
def attemptAutoProofSMT (name : Name) (type : Expr) : TermElabM Bool := do
  let mvar ← mkFreshExprMVar type
  let goal := mvar.mvarId!

  try
    -- Run auto tactic directly
    let remainingGoals ← Tactic.run goal do
      -- The auto tactic will use SMT if configured
      evalTactic (← `(tactic| auto))

    if remainingGoals.isEmpty then
      IO.println s!"✓ PROVED by auto (SMT): {name}"
      return true
  catch e =>
    -- Auto failed, try with intros
    try
      let remainingGoals ← Tactic.run goal do
        evalTactic (← `(tactic| intros; auto))

      if remainingGoals.isEmpty then
        IO.println s!"✓ PROVED by intros;auto (SMT): {name}"
        return true
    catch _ => pure ()

  return false

-- Repeated from TestBench.lean
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

-- Run smt-auto prover on MiniF2F benchmark
def runSMTAutoAnalysis : TermElabM Unit := do
  IO.println "MiniF2F smt-auto Prover Analysis:"
  IO.println "=================================="

  let theorems ← extractMiniF2FTheorems

  let mut count := 0
  let mut proved := 0

  for (name, info) in theorems do
    match info with
    | .thmInfo thmInfo =>
      count := count + 1
      let isProved ← attemptAutoProofSMT name thmInfo.type
      if isProved then
        proved := proved + 1
        --IO.println s!"✓ PROVED {name} with {result.get!}"
    | _ => pure ()
  IO.println s!"\nProver Summary:"
  IO.println s!"- Total theorems: {count}"
  IO.println s!"- Proved: {proved}"
  IO.println s!"- Success rate: {(proved.toFloat / count.toFloat * 100).round}%"

#eval runSMTAutoAnalysis.run'

def main : IO Unit := do
  IO.println "Analysis run complete."
