import LeanDisco
import MiniF2F.Valid
import Lean

open Lean Meta Elab

-- Function to check if an expression contains 'sorry'
def hasSorryExpr (e : Expr) : Bool :=
  match e with
  | .const name _ => name == ``sorryAx
  | .app f a => hasSorryExpr f || hasSorryExpr a
  | .lam _ _ body _ => hasSorryExpr body
  | .forallE _ _ body _ => hasSorryExpr body
  | .letE _ _ value body _ => hasSorryExpr value || hasSorryExpr body
  | .mdata _ e => hasSorryExpr e
  | .proj _ _ e => hasSorryExpr e
  | _ => false

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

    -- Check if the proof contains 'sorry'
    let hasProof := !hasSorryExpr thmInfo.value
    if hasProof then
      IO.println "Status: Has complete proof"
    else
      IO.println "Status: Contains sorry (incomplete)"
    IO.println "---"
  | _ => pure ()

-- Main metaprogramming function
def runMiniF2FAnalysis : MetaM Unit := do
  IO.println "MiniF2F Benchmark Analysis (via Metaprogramming):"
  IO.println "================================================="

  let theorems ← extractMiniF2FTheorems
  IO.println s!"Found {theorems.length} theorems"
  IO.println ""

  for (name, info) in theorems do
    analyzeTheorem name info

-- Use #eval! to run the metaprogramming analysis (ignoring sorry warnings)
#eval runMiniF2FAnalysis.run'

def main : IO Unit := do
  IO.println "Run complete. See analysis above."
