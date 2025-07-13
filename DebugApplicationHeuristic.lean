import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

/-- Add enhanced debug output to the application heuristic to understand why it generates 0 concepts -/
def debugApplicationHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []

  IO.println "[DEBUG_APP] Starting application heuristic analysis..."

  -- Separate concepts by generation method for better targeting
  let seedFunctions := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if !t.hasLooseBVars && !v.hasLooseBVars && (m.generationMethod == "seed" || m.generationMethod == "mined") && t.isForall then
        some (n, t, v, d, m)
      else none
    | _ => none

  let allArgs := concepts.filterMap fun c => match c with
    | ConceptData.definition n t v _ d m =>
      if !t.hasLooseBVars && !v.hasLooseBVars && m.specializationDepth <= 1 then
        some (n, t, v, d, m)
      else none
    | _ => none

  IO.println s!"[DEBUG_APP] Found {seedFunctions.length} seed functions, {allArgs.length} potential arguments"

  -- Enhanced debugging: show actual function/arg details
  IO.println "[DEBUG_APP] Seed functions analysis:"
  for (fname, ftype, fvalue, fdeps, fmetadata) in seedFunctions.take 5 do  -- Show first 5
    IO.println s!"  Function: {fname}"
    IO.println s!"    Generation method: {fmetadata.generationMethod}"
    IO.println s!"    Type has loose BVars: {ftype.hasLooseBVars}"
    IO.println s!"    Value has loose BVars: {fvalue.hasLooseBVars}"
    IO.println s!"    Type is forall: {ftype.isForall}"

  IO.println "[DEBUG_APP] Potential arguments analysis:"
  for (aname, atype, avalue, adeps, ametadata) in allArgs.take 5 do  -- Show first 5
    IO.println s!"  Argument: {aname}"
    IO.println s!"    Generation method: {ametadata.generationMethod}"
    IO.println s!"    Specialization depth: {ametadata.specializationDepth}"
    IO.println s!"    Type has loose BVars: {atype.hasLooseBVars}"
    IO.println s!"    Value has loose BVars: {avalue.hasLooseBVars}"

  -- Strategy 1: Apply seed functions to all suitable arguments with detailed logging
  let mut totalAttempts := 0
  let mut compatibilityFailures := 0
  let mut alreadyTriedCount := 0
  let mut successfulApplications := 0
  let mut exceptionCount := 0

  for (fname, ftype, fvalue, fdeps, fmetadata) in seedFunctions do
    IO.println s!"[DEBUG_APP] Processing seed function: {fname}"
    
    -- Skip normalization to prevent infinite recursion
    match ftype with
    | .forallE _ argType _ _ =>
      IO.println s!"[DEBUG_APP]   Function {fname} expects argument type"
      let mut applicationCount := 0
      for (aname, _, avalue, adeps, ametadata) in allArgs do
        totalAttempts := totalAttempts + 1
        
        if applicationCount >= 5 then  -- Limit per function
          IO.println s!"[DEBUG_APP]   Reached application limit for {fname}"
          break

        let proposedName := s!"{fname}_applied_to_{aname}"
        let alreadyTried := concepts.any (fun c => getConceptName c == proposedName)

        if alreadyTried then
          alreadyTriedCount := alreadyTriedCount + 1
          IO.println s!"[DEBUG_APP]   Skipping {proposedName} - already tried"
        else if fname == aname then
          IO.println s!"[DEBUG_APP]   Skipping {proposedName} - self-application"
        else
          IO.println s!"[DEBUG_APP]   Attempting application: {fname} to {aname}"
          
          try
            let atype ← safeInferType avalue
            let compatible ← safeIsDefEq atype argType
            
            if compatible then
              IO.println s!"[DEBUG_APP]     Types are compatible!"
              let resultValue := mkApp fvalue avalue
              if !resultValue.hasLooseBVars then
                let resultType ← safeInferType resultValue
                IO.println s!"[DEBUG_APP]     Successfully created application result"

                let newMeta := {
                  name := proposedName
                  created := 0
                  parent := some fname
                  interestingness := 0.7
                  useCount := 0
                  successCount := 0
                  specializationDepth := ametadata.specializationDepth + 1
                  generationMethod := "application"
                }
                newConcepts := newConcepts ++ [
                  ConceptData.definition proposedName resultType resultValue none (fdeps ++ adeps ++ [aname]) newMeta
                ]
                applicationCount := applicationCount + 1
                successfulApplications := successfulApplications + 1
                IO.println s!"[DEBUG_APP]     ✅ SUCCESS: Created {proposedName}"
              else
                IO.println s!"[DEBUG_APP]     ❌ Result has loose bound variables"
            else
              compatibilityFailures := compatibilityFailures + 1
              IO.println s!"[DEBUG_APP]     ❌ Type incompatibility"
          catch e =>
            exceptionCount := exceptionCount + 1
            IO.println s!"[DEBUG_APP]     ❌ Exception: {toString e}"
    | _ => 
      IO.println s!"[DEBUG_APP]   Function {fname} is not a forall type"

  -- Final summary
  IO.println s!"[DEBUG_APP] === APPLICATION HEURISTIC SUMMARY ==="
  IO.println s!"[DEBUG_APP] Total attempts: {totalAttempts}"
  IO.println s!"[DEBUG_APP] Already tried: {alreadyTriedCount}"
  IO.println s!"[DEBUG_APP] Type incompatibilities: {compatibilityFailures}"
  IO.println s!"[DEBUG_APP] Exceptions: {exceptionCount}"
  IO.println s!"[DEBUG_APP] Successful applications: {successfulApplications}"
  IO.println s!"[DEBUG_APP] New concepts created: {newConcepts.length}"

  return newConcepts

/-- Test using the debug version with actual benchmark data -/
def testWithRealData : MetaM Unit := do
  IO.println "=== Testing Debug Application Heuristic with Real Data ==="
  
  -- Import some basic mathematical concepts (simulated)
  let testConcepts := [
    -- Simulate a seed function (addition)
    ConceptData.definition 
      "Nat.add"
      sorry  -- Type: Nat → Nat → Nat
      sorry  -- Value: addition function
      none
      []
      { name := "Nat.add"
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "seed" },
        
    -- Simulate some arguments
    ConceptData.definition
      "five"
      sorry  -- Type: Nat
      sorry  -- Value: 5
      none
      []
      { name := "five"
        created := 0
        parent := none
        interestingness := 1.0
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "seed" }
  ]
  
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    enableDebugOutput := true
  }
  
  let results ← debugApplicationHeuristic config testConcepts
  IO.println s!"Final result: {results.length} concepts generated"

#eval! testWithRealData