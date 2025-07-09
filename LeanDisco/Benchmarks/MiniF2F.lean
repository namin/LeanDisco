import Lean
import LeanDisco.Benchmarks.Core

namespace LeanDisco.Benchmarks.MiniF2F

open Lean

/-- JSON structure for miniF2F problems -/
structure MiniF2FProblem where
  name : String
  split : String
  formal_statement : String
  header : String
  informal_statement : Option String := none
  informal_proof : Option String := none
  deriving FromJson, ToJson

/-- Extract category from problem name (e.g., "algebra" from "algebra_2rootspoly_apatapbeq2asqp2ab") -/
def extractCategory (name : String) : String :=
  match name.splitOn "_" with
  | cat :: _ => cat
  | [] => "uncategorized"

/-- Convert MiniF2F problem to our Problem structure -/
def toProblem (mf2f : MiniF2FProblem) : Problem :=
  { id := mf2f.name
    name := mf2f.name
    formalStatement := mf2f.formal_statement
    header := mf2f.header
    informalStatement := mf2f.informal_statement
    informalProof := mf2f.informal_proof
    split := mf2f.split
    category := some (extractCategory mf2f.name)
  }

/-- Load miniF2F problems from JSONL file -/
def loadProblems (path : System.FilePath) (split : Option String := none) : IO (Array Problem) := do
  let content ← IO.FS.readFile path
  let lines := content.trim.splitOn "\n" |>.filter (·.length > 0)
  
  let mut problems : Array Problem := #[]
  
  for line in lines do
    try
      let json ← match Json.parse line with
        | .ok j => pure j
        | .error e => throw (IO.userError s!"JSON parse error: {e}")
      let mf2fProblem : MiniF2FProblem ← match fromJson? json with
        | .ok p => pure p
        | .error e => throw (IO.userError s!"JSON decode error: {e}")
      let problem := toProblem mf2fProblem
      
      -- Filter by split if specified
      if split.isNone || split == some problem.split then
        problems := problems.push problem
    catch e =>
      IO.eprintln s!"Error parsing line: {e}"
      continue
  
  return problems

/-- Get problems grouped by category -/
def groupByCategory (problems : Array Problem) : Std.HashMap String (Array Problem) := 
  problems.foldl (init := Std.HashMap.empty) fun acc p =>
    let cat := p.category.getD "uncategorized"
    match acc[cat]? with
    | some ps => acc.insert cat (ps.push p)
    | none => acc.insert cat #[p]

/-- Filter problems by difficulty based on naming conventions -/
def filterByDifficulty (problems : Array Problem) (difficulty : String) : Array Problem :=
  problems.filter fun p =>
    -- This is a heuristic - adjust based on actual miniF2F naming
    match difficulty with
    | "easy" => contains p.name "basic" || contains p.name "simple"
    | "medium" => !(contains p.name "basic") && !(contains p.name "hard")
    | "hard" => contains p.name "hard" || contains p.name "advanced"
    | _ => true

end LeanDisco.Benchmarks.MiniF2F