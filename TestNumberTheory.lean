import LeanDisco
import LeanDisco.Domains.NumberTheory

open Lean Meta Elab

def myConfig : DiscoveryConfig := {
  maxIterations := 5,
  logProgress := true,
  enableProofSearch := true,
  logEachConjecture := true,
  logProofSuccess := true,
  logProofFailure := true
}

-- First, let's test the pattern analysis functions
#eval show MetaM Unit from do
  logInfo m!"=== Testing Number Theory Pattern Discovery ==="

  -- Test modulo pattern discovery
  let mod4vals := LeanDisco.Domains.NumberTheory.analyzeModulo (fun n => n^2) 4 20
  logInfo m!"n² mod 4 takes values: {mod4vals}"

  let mod7vals := LeanDisco.Domains.NumberTheory.analyzeModulo (fun n => n^3) 7 20
  logInfo m!"n³ mod 7 takes values: {mod7vals}"

  -- Test period finding
  let fibMod10 := (List.range 30).map fun n =>
    let rec fib : ℕ → ℕ
      | 0 => 0
      | 1 => 1
      | n+2 => fib n + fib (n+1)
    fib n % 10

  match LeanDisco.Domains.NumberTheory.findPeriod fibMod10 20 with
  | some p => logInfo m!"Fibonacci mod 10 has period: {p}"
  | none => logInfo m!"No period found"

-- Now run the full discovery system
#eval show MetaM Unit from do
  let final ← runDiscoveryWith [
    LeanDisco.Domains.NumberTheory.heuristicModuloPatterns,
    LeanDisco.Domains.NumberTheory.heuristicPerfectSquares,
    LeanDisco.Domains.NumberTheory.heuristicPrimePatterns,
    LeanDisco.Domains.NumberTheory.heuristicLogModuloDiscoveries,
    heuristicProveUnproven myConfig
  ] myConfig (by exact LeanDisco.Domains.NumberTheory.NumberTheoryDomain)

  logInfo m!"{String.mk (List.replicate 60 '=')}"
  logInfo m!"Final iteration: {final.iteration}"
  logInfo m!"Total concepts: {final.concepts.size}"

  -- Count by tags
  let modConcepts := final.concepts.filter (fun c => "modulo" ∈ c.tags)
  let primesConcepts := final.concepts.filter (fun c => "primes" ∈ c.tags)
  let provenConcepts := final.concepts.filter (fun c => c.proof?.isSome)

  logInfo m!"Modulo patterns found: {modConcepts.size}"
  logInfo m!"Prime patterns found: {primesConcepts.size}"
  logInfo m!"Proven theorems: {provenConcepts.size}"

  -- Show some discoveries (from the final state, not the initial concepts)
  logInfo m!"\n📊 Sample Discoveries:"
  let finalModConcepts := final.concepts.filter (fun c => "modulo" ∈ c.tags)
  for concept in finalModConcepts.toList.take 5 do
    let status := if concept.proof?.isSome then "✅" else "❓"
    logInfo m!"  {status} {concept.name}"
