import LeanDisco.Domains.NumberTheory

set_option maxHeartbeats 1000000000

open LeanDisco.Domains.NumberTheory

#eval runNumberTheoryDiscovery
  { includeBasicArithmetic := true
    includeDivisibility := true
    includePrimeTheory := true
    includeModularArithmetic := true
    includeSequences := true
    includeDiophantine := false  -- Start simple
    maxNumber := 50 }            -- Keep it manageable
  { maxSpecializationDepth := 3
    maxConceptsPerIteration := 50
    enableConjectures := true
    enablePatternRecognition := true
    enableDebugOutput := true }
  4  -- iterations