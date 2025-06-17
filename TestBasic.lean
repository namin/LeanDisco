import LeanDisco.Basic

open LeanDisco

#eval do
  let config : DiscoveryConfig := { maxSpecializationDepth := 2, maxConceptsPerIteration := 10 }
  let kb ← initializeSystem config false
  IO.println s!"Basic test: {kb.concepts.length} initial concepts"
  IO.println s!"Enhanced heuristics count: {kb.heuristics.entries.length}"
  pure ()