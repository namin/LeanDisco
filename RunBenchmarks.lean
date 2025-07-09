import LeanDisco.Benchmarks

open LeanDisco.Benchmarks

def main (args : List String) : IO Unit := do
  match args with
  | ["test"] =>
    -- Quick test with synthetic problems
    IO.println "Running quick test..."
    quickTest
  
  | ["run", benchmarkFile] =>
    -- Run full benchmark suite
    let path := System.FilePath.mk benchmarkFile
    if ← path.pathExists then
      runBenchmarks path
    else
      IO.eprintln s!"Benchmark file not found: {benchmarkFile}"
  
  | ["run", benchmarkFile, "--filter", split] =>
    -- Run filtered benchmarks (train/valid/test)
    let path := System.FilePath.mk benchmarkFile
    if ← path.pathExists then
      runBenchmarks path {} (some split)
    else
      IO.eprintln s!"Benchmark file not found: {benchmarkFile}"
  
  | ["run", benchmarkFile, "--category", category] =>
    -- Run specific category
    let path := System.FilePath.mk benchmarkFile
    if ← path.pathExists then
      runCategoryBenchmarks path category
    else
      IO.eprintln s!"Benchmark file not found: {benchmarkFile}"
  
  | ["run", benchmarkFile, "--verbose"] =>
    -- Run with verbose output
    let path := System.FilePath.mk benchmarkFile
    if ← path.pathExists then
      runBenchmarks path { verbose := true }
    else
      IO.eprintln s!"Benchmark file not found: {benchmarkFile}"
  
  | ["run", benchmarkFile, "--parallel", "false"] =>
    -- Run sequentially (for debugging)
    let path := System.FilePath.mk benchmarkFile
    if ← path.pathExists then
      runBenchmarks path { parallel := false }
    else
      IO.eprintln s!"Benchmark file not found: {benchmarkFile}"
  
  | ["compare", beforeFile, afterFile] =>
    -- Compare two benchmark runs
    let before := System.FilePath.mk beforeFile
    let after := System.FilePath.mk afterFile
    if (← before.pathExists) && (← after.pathExists) then
      compareBenchmarkRuns before after
    else
      IO.eprintln "One or both result files not found"
  
  | _ =>
    -- Show usage
    IO.println "LeanDisco Benchmark Runner"
    IO.println ""
    IO.println "Usage:"
    IO.println "  lake exe runBenchmarks test"
    IO.println "    Run quick test with synthetic problems"
    IO.println ""
    IO.println "  lake exe runBenchmarks run <benchmark_file>"
    IO.println "    Run full benchmark suite"
    IO.println ""
    IO.println "  lake exe runBenchmarks run <benchmark_file> --filter <train|valid|test>"
    IO.println "    Run only problems from specified split"
    IO.println ""
    IO.println "  lake exe runBenchmarks run <benchmark_file> --category <category>"
    IO.println "    Run only problems from specified category"
    IO.println ""
    IO.println "  lake exe runBenchmarks run <benchmark_file> --verbose"
    IO.println "    Run with verbose output"
    IO.println ""
    IO.println "  lake exe runBenchmarks run <benchmark_file> --parallel false"
    IO.println "    Run sequentially instead of in parallel"
    IO.println ""
    IO.println "  lake exe runBenchmarks compare <before_results.json> <after_results.json>"
    IO.println "    Compare two benchmark runs"
    IO.println ""
    IO.println "Example:"
    IO.println "  lake exe runBenchmarks run benchmarks/miniF2F-lean4/minif2f_lean4.jsonl --filter test"