import Lean
import LeanDisco.Basic

namespace LeanDisco.Benchmarks

/-- Benchmark problem representation -/
structure Problem where
  id : String
  name : String
  formalStatement : String
  header : String
  informalStatement : Option String := none
  informalProof : Option String := none
  split : String  -- train/valid/test
  category : Option String := none
  deriving Repr, BEq

/-- Result of evaluating a single problem -/
structure EvalResult where
  problemId : String
  success : Bool
  proof : Option String := none
  timeMs : Nat
  conceptsExplored : Nat
  conceptsUsed : List String := []  -- Track which concepts helped
  heuristicsApplied : List String := []  -- Track which heuristics were used
  errorMsg : Option String := none
  deriving Repr

/-- Configuration for benchmark evaluation -/
structure EvalConfig where
  timeoutMs : Nat := 60000  -- Increased from 30s to 60s
  maxConcepts : Nat := 5000  -- Increased to leverage LeanDisco's capabilities
  maxDepth : Nat := 10
  strategies : List String := ["apply", "compose", "specialize", "pattern_match"]
  verbose : Bool := false
  parallel : Bool := true  -- Enable parallel evaluation
  useDiscoverySystem : Bool := true  -- Use full LeanDisco system
  deriving Repr

/-- Summary statistics for evaluation run -/
structure EvalSummary where
  totalProblems : Nat
  solvedProblems : Nat
  totalTimeMs : Nat
  avgTimeMs : Nat
  avgConceptsExplored : Nat
  resultsByCategory : List (String × Nat × Nat)
  topConcepts : List (String × Nat)  -- Most successful concepts
  topHeuristics : List (String × Nat)  -- Most successful heuristics
  deriving Repr

def EvalSummary.successRate (s : EvalSummary) : Float :=
  if s.totalProblems == 0 then 0.0 
  else s.solvedProblems.toFloat / s.totalProblems.toFloat * 100

def EvalSummary.toString (s : EvalSummary) : String :=
  s!"Evaluation Summary:\n" ++
  s!"  Total Problems: {s.totalProblems}\n" ++
  s!"  Solved: {s.solvedProblems} ({s.successRate.toUInt8}%)\n" ++
  s!"  Total Time: {s.totalTimeMs}ms\n" ++
  s!"  Avg Time per Problem: {s.avgTimeMs}ms\n" ++
  s!"  Avg Concepts Explored: {s.avgConceptsExplored}\n" ++
  s!"  Results by Category:\n" ++
  String.intercalate "\n" (s.resultsByCategory.map fun (cat, solved, total) =>
    s!"    {cat}: {solved}/{total} ({(solved.toFloat / total.toFloat * 100).toUInt8}%)") ++
  s!"\n  Top Concepts:\n" ++
  String.intercalate "\n" (s.topConcepts.take 5 |>.map fun (concept, count) =>
    s!"    {concept}: {count} proofs") ++
  s!"\n  Top Heuristics:\n" ++
  String.intercalate "\n" (s.topHeuristics.take 5 |>.map fun (heuristic, count) =>
    s!"    {heuristic}: {count} applications")

instance : ToString EvalSummary := ⟨EvalSummary.toString⟩

end LeanDisco.Benchmarks