import Lean
import LeanDisco.Basic

namespace LeanDisco.Benchmarks.ProofValidation

open Lean Meta Elab Term

/-- Validate a proof term against a formal statement using Lean's type checker -/
def validateProofTerm (stmt : String) (proof : String) : TermElabM Bool := do
  try
    -- Parse the statement
    let stmtStx ← match Parser.runParserCategory (← getEnv) `term stmt with
      | .ok stx => pure stx
      | .error err => throwError "Failed to parse statement: {err}"
    
    -- Parse the proof
    let proofStx ← match Parser.runParserCategory (← getEnv) `term proof with
      | .ok stx => pure stx  
      | .error err => throwError "Failed to parse proof: {err}"
    
    -- Elaborate the statement to get its type
    let stmtExpr ← elabTerm stmtStx none
    let stmtType ← inferType stmtExpr
    
    -- Elaborate the proof with expected type
    let proofExpr ← elabTermEnsuringType proofStx stmtType
    
    -- Check if the proof has the correct type
    let proofType ← inferType proofExpr
    if ← isDefEq proofType stmtType then
      return true
    else
      return false
  catch _ =>
    return false

/-- Validate using external process as fallback (for complex imports) -/
def validateProofExternal (header : String) (stmt : String) (proof : String) : IO Bool := do
  try
    -- Create temporary file with the proof attempt
    let tempContent := s!"{header}\n\n#check ({proof} : {stmt})\n"
    let tempFile := System.FilePath.mk s!"/tmp/lean_proof_{← IO.monoMsNow}.lean"
    IO.FS.writeFile tempFile tempContent
    
    -- Try to compile it
    let result ← IO.Process.spawn {
      cmd := "lake"
      args := #["lean", tempFile.toString]
      cwd := some "./"  -- Use current directory
    }
    let exitCode ← result.wait
    
    -- Clean up
    IO.FS.removeFile tempFile
    
    return exitCode == 0
  catch _ =>
    return false

/-- Try multiple proof strategies and validate them -/
def tryProofStrategies (stmt : String) (strategies : List String) : TermElabM (Option String) := do
  for strategy in strategies do
    let isValid ← validateProofTerm stmt strategy
    if isValid then
      return some strategy
  return none

/-- Common proof tactics for benchmarks -/
def commonTactics : List String := [
  "rfl",
  "trivial", 
  "decide",
  "by simp",
  "by ring",
  "by norm_num",
  "by linarith",
  "by omega",
  "by abel",
  "by field_simp",
  "by simp [*]",
  "by simp_all",
  "by aesop",
  "fun _ => rfl",
  "fun _ => by simp",
  "fun _ => by ring",
  "fun _ _ => by ring",
  "fun _ _ => by simp"
]

/-- Validate a discovered proof concept -/
def validateDiscoveredProof (concept : ConceptData) (targetStmt : String) : TermElabM Bool := do
  match concept with
  | ConceptData.theorem _ stmt _ _ _ =>
    -- Check if this theorem proves our target by comparing expressions
    let env ← getEnv
    let targetStx ← match Parser.runParserCategory env `term targetStmt with
      | .ok stx => pure stx
      | .error _ => return false
    let targetExpr ← elabTerm targetStx none
    isDefEq stmt targetExpr
  | _ => return false

/-- Extract proof term from a concept -/
def extractProofFromConcept (concept : ConceptData) : Option String :=
  match concept with
  | ConceptData.theorem name _ _ _ _ => some s!"by exact {name}"
  | ConceptData.heuristicRef name _ _ => some s!"by {name}"
  | ConceptData.taskRef name _ _ => some s!"by {name}"
  | _ => none

end LeanDisco.Benchmarks.ProofValidation