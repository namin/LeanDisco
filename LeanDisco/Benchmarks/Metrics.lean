import Lean
import LeanDisco.Benchmarks.Core

namespace LeanDisco.Benchmarks.Metrics

open Lean

/-- Compute evaluation summary from results -/
def computeSummary (results : Array EvalResult) : EvalSummary :=
  let solved := results.filter (·.success)
  let totalTime := results.foldl (·+·.timeMs) 0
  let totalConcepts := results.foldl (·+·.conceptsExplored) 0
  
  -- Group by category
  let categoryMap := results.foldl (init := Std.HashMap.empty) fun acc r =>
    let cat := r.problemId.splitOn "_" |>.head? |>.getD "unknown"
    let (solved, total) := match acc[cat]? with
      | some (s, t) => (s, t)
      | none => (0, 0)
    if r.success then
      acc.insert cat (solved + 1, total + 1)
    else
      acc.insert cat (solved, total + 1)
  
  let resultsByCategory := categoryMap.toList.map fun (cat, (solved, total)) =>
    (cat, solved, total)
  
  -- Track concept usage
  let conceptCounts := results.foldl (init := Std.HashMap.empty) fun acc r =>
    r.conceptsUsed.foldl (init := acc) fun acc' concept =>
      let count := match acc'[concept]? with | some c => c | none => 0
      acc'.insert concept (count + 1)
  
  let topConcepts := conceptCounts.toList.mergeSort (fun a b => a.2 > b.2)
  
  -- Track heuristic usage
  let heuristicCounts := results.foldl (init := Std.HashMap.empty) fun acc r =>
    r.heuristicsApplied.foldl (init := acc) fun acc' heuristic =>
      let count := match acc'[heuristic]? with | some c => c | none => 0
      acc'.insert heuristic (count + 1)
  
  let topHeuristics := heuristicCounts.toList.mergeSort (fun a b => a.2 > b.2)
  
  { totalProblems := results.size
    solvedProblems := solved.size
    totalTimeMs := totalTime
    avgTimeMs := if results.isEmpty then 0 else totalTime / results.size
    avgConceptsExplored := if results.isEmpty then 0 else totalConcepts / results.size
    resultsByCategory := resultsByCategory.mergeSort (fun a b => a.1 < b.1)
    topConcepts := topConcepts
    topHeuristics := topHeuristics
  }

/-- Save evaluation results to JSON -/
def saveResults (results : Array EvalResult) (path : System.FilePath) : IO Unit := do
  let json := Json.arr (results.map fun r => Json.mkObj [
    ("problemId", Json.str r.problemId),
    ("success", Json.bool r.success),
    ("proof", Json.str (r.proof.getD "")),
    ("timeMs", Json.num r.timeMs),
    ("conceptsExplored", Json.num r.conceptsExplored),
    ("conceptsUsed", Json.arr (r.conceptsUsed.toArray.map Json.str)),
    ("heuristicsApplied", Json.arr (r.heuristicsApplied.toArray.map Json.str)),
    ("errorMsg", Json.str (r.errorMsg.getD ""))
  ])
  IO.FS.writeFile path json.pretty

/-- Load evaluation results from JSON -/
def loadResults (path : System.FilePath) : IO (Array EvalResult) := do
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .ok (Json.arr results) =>
    results.mapM fun json => do
      match json.getObj? with
      | .ok obj =>
        let problemId := (obj["problemId"]?).bind (·.getStr?) |>.getD ""
        let success := (obj["success"]?).bind (·.getBool?) |>.getD false
        let proof := (obj["proof"]?).bind (·.getStr?) |>.filter (·.length > 0)
        let timeMs := (obj["timeMs"]?).bind (·.getNat?) |>.getD 0
        let conceptsExplored := (obj["conceptsExplored"]?).bind (·.getNat?) |>.getD 0
        let conceptsUsed := match obj["conceptsUsed"]? with
          | some (Json.arr cs) => cs.filterMap (·.getStr?) |>.toList
          | _ => []
        let heuristicsApplied := match obj["heuristicsApplied"]? with
          | some (Json.arr hs) => hs.filterMap (·.getStr?) |>.toList
          | _ => []
        let errorMsg := (obj["errorMsg"]?).bind (·.getStr?) |>.filter (·.length > 0)
        return EvalResult.mk problemId success proof timeMs conceptsExplored conceptsUsed heuristicsApplied errorMsg
      | .error _ => return EvalResult.mk "" false none 0 0 [] [] (some "JSON parse error")
  | _ => return #[]

/-- Generate detailed report -/
def generateReport (results : Array EvalResult) (outputPath : System.FilePath) : IO Unit := do
  let summary := computeSummary results
  let timestamp := toString (← IO.monoMsNow)
  let report := s!"# LeanDisco Benchmark Evaluation Report\n\n" ++
    s!"Generated: {timestamp}\n\n" ++
    s!"{summary}\n\n" ++
    s!"## Detailed Results\n\n"
  
  -- Add problem-by-problem results
  let problemDetails := results.map fun r =>
    s!"- **{r.problemId}**: " ++
    (if r.success then s!"✓ Solved in {r.timeMs}ms" else s!"✗ Failed") ++
    (if let some proof := r.proof then s!" (Proof: `{proof}`)" else "") ++
    (if let some err := r.errorMsg then s!" (Error: {err})" else "") ++
    s!" [Concepts: {r.conceptsExplored}]"
  
  let fullReport := report ++ String.intercalate "\n" problemDetails.toList
  
  IO.FS.writeFile outputPath fullReport

/-- Compare two evaluation runs -/
def compareRuns (before : Array EvalResult) (after : Array EvalResult) : String :=
  let beforeSummary := computeSummary before
  let afterSummary := computeSummary after
  
  let improvement := afterSummary.successRate - beforeSummary.successRate
  let speedup := if beforeSummary.avgTimeMs > 0 
    then (beforeSummary.avgTimeMs.toFloat - afterSummary.avgTimeMs.toFloat) / beforeSummary.avgTimeMs.toFloat * 100
    else 0.0
  
  s!"Comparison:\n" ++
  s!"  Success Rate: {beforeSummary.successRate.toUInt8}% → {afterSummary.successRate.toUInt8}% " ++
  s!"({if improvement >= 0 then "+" else ""}{improvement.toUInt8}%)\n" ++
  s!"  Avg Time: {beforeSummary.avgTimeMs}ms → {afterSummary.avgTimeMs}ms " ++
  s!"({if speedup >= 0 then "+" else ""}{speedup.toUInt8}% speedup)\n" ++
  s!"  Problems Solved: {beforeSummary.solvedProblems} → {afterSummary.solvedProblems}"

end LeanDisco.Benchmarks.Metrics