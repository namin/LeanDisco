import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open LeanDisco
open Lean Meta Elab Term

/-- Test the application heuristic in isolation -/
def testApplicationHeuristic : MetaM Unit := do
  IO.println "=== Testing Application Heuristic in Isolation ==="
  
  -- Create a simple seed function and argument
  let simpleFunc : ConceptData := ConceptData.definition 
    "test_add_one"
    (← mkForallFVars #[] (mkArrow (mkConst ``Nat) (mkConst ``Nat)))
    (← mkLambdaFVars #[] (mkLam `x (mkConst ``Nat) (mkApp2 (mkConst ``Nat.add) (mkBVar 0) (mkNatLit 1)) .default))
    none
    []
    { name := "test_add_one"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed" }
      
  let simpleArg : ConceptData := ConceptData.definition
    "test_five"
    (mkConst ``Nat)
    (mkNatLit 5)
    none
    []
    { name := "test_five"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed" }
  
  let inputConcepts := [simpleFunc, simpleArg]
  
  IO.println s!"Created {inputConcepts.length} test concepts:"
  for c in inputConcepts do
    IO.println s!"  - {getConceptName c} ({getConceptMetadata c |>.generationMethod})"
  
  -- Configure for minimal debug
  let config : DiscoveryConfig := {
    maxSpecializationDepth := 2
    maxConceptsPerIteration := 20
    pruneThreshold := 0.5
    deduplicateConcepts := false  -- Disable to see raw output
    canonicalizeConcepts := false  -- Disable to see raw output
    filterInternalProofs := false  -- Disable to see raw output
    enableConjectures := true
    enablePatternRecognition := false
    enableDebugOutput := true
  }
  
  -- Run application heuristic
  IO.println "\n=== Running Application Heuristic ==="
  let results ← applicationHeuristic config inputConcepts
  
  IO.println s!"\n=== Results: {results.length} new concepts generated ===""
  if results.isEmpty then
    IO.println "❌ NO CONCEPTS GENERATED!"
    
    -- Debug: Check what the heuristic found
    let seedFunctions := inputConcepts.filterMap fun c => match c with
      | ConceptData.definition n t v _ d m =>
        if !t.hasLooseBVars && !v.hasLooseBVars && (m.generationMethod == "seed" || m.generationMethod == "mined") && t.isForall then
          some (n, t, v, d, m)
        else none
      | _ => none
    
    let allArgs := inputConcepts.filterMap fun c => match c with
      | ConceptData.definition n t v _ d m =>
        if !t.hasLooseBVars && !v.hasLooseBVars && m.specializationDepth <= 1 then
          some (n, t, v, d, m)
        else none
      | _ => none
    
    IO.println s!"Debug: Found {seedFunctions.length} seed functions, {allArgs.length} potential arguments"
    
    for (fname, ftype, fvalue, fdeps, fmetadata) in seedFunctions do
      IO.println s!"Seed function: {fname}"
      IO.println s!"  Type: {← ppExpr ftype}"
      IO.println s!"  Has loose BVars: {ftype.hasLooseBVars}"
      IO.println s!"  Is forall: {ftype.isForall}"
      
      match ftype with
      | .forallE _ argType _ _ =>
        IO.println s!"  Expected arg type: {← ppExpr argType}"
        for (aname, atype, avalue, adeps, ametadata) in allArgs do
          IO.println s!"  Testing arg: {aname}"
          let actualArgType ← safeInferType avalue
          IO.println s!"    Arg type: {← ppExpr actualArgType}"
          let compatible ← safeIsDefEq actualArgType argType
          IO.println s!"    Compatible: {compatible}"
      | _ =>
        IO.println s!"  Not a forall type!"
  else
    for c in results do
      IO.println s!"✅ Generated: {getConceptName c}"

/-- Run the test -/
#eval! testApplicationHeuristic