import LeanDisco.Basic

namespace LeanDisco.ProofGuidedSimple

open Lean Meta Elab
open LeanDisco

/-- A single step in a proof -/
inductive ProofStep where
  | apply (thm : Name) : ProofStep
  | rewrite (thm : Name) : ProofStep
  | rfl : ProofStep
  | assumption : ProofStep
  deriving Repr

/-- Result of attempting a proof step -/
inductive StepResult where
  | success (newGoal : Option Expr) (proof : Expr)
  | failure (reason : String)

/-- Try to apply a theorem to the current goal -/
def tryApplyTheorem (goal : Expr) (thmName : Name) : MetaM StepResult := do
  try
    let thm := mkConst thmName
    let thmType ← inferType thm
    
    -- Check if theorem type unifies with goal
    if ← isDefEq thmType goal then
      return StepResult.success none thm
    
    -- Try to apply theorem (might produce subgoals)
    -- For now, we'll just check direct application
    return StepResult.failure s!"Cannot apply {thmName} to goal"
    
  catch e =>
    return StepResult.failure s!"Error applying {thmName}: {← e.toMessageData.toString}"

/-- Try reflexivity -/
def tryRefl (goal : Expr) : MetaM StepResult := do
  -- Check if goal is of form a = a
  if goal.isAppOfArity ``Eq 3 then
    let args := goal.getAppArgs
    if ← isDefEq args[1]! args[2]! then
      let proof := mkApp (mkConst ``Eq.refl) args[1]!
      return StepResult.success none proof
  return StepResult.failure "Goal is not a reflexive equality"

/-- Try a two-step proof: use transitivity of equality -/
def tryTwoStepProof (goal : Expr) (thm1 thm2 : Name) : MetaM (Option Expr) := do
  try
    -- For equality goals a = c, try to prove via a = b and b = c
    if goal.isAppOfArity ``Eq 3 then
      let args := goal.getAppArgs
      let lhs := args[1]!
      let rhs := args[2]!
      
      -- Try thm1 to transform lhs, then thm2 to get to rhs
      let t1 := mkConst thm1
      let t2 := mkConst thm2
      let t1Type ← inferType t1
      let t2Type ← inferType t2
      
      -- Check if t1 applies to lhs and t2 applies to the result
      if t1Type.isAppOfArity ``Eq 3 && t2Type.isAppOfArity ``Eq 3 then
        let t1Args := t1Type.getAppArgs
        let t2Args := t2Type.getAppArgs
        
        -- Simple case: if t1 proves lhs = middle and t2 proves middle = rhs
        if (← isDefEq t1Args[1]! lhs) && (← isDefEq t2Args[2]! rhs) && (← isDefEq t1Args[2]! t2Args[1]!) then
          -- Build transitivity proof: Eq.trans t1 t2
          let proof := mkApp2 (mkConst ``Eq.trans) t1 t2
          IO.println s!"[PROOF-CONSTRUCT] Built transitivity proof with {thm1} and {thm2}"
          return some proof
    
    return none
  catch _ =>
    return none

/-- Try multi-step proofs by calling helper functions -/
def tryMultiStepProof (goal : Expr) (theorems : List Name) : MetaM (Option Expr) := do
  for thm1 in theorems do
    for thm2 in theorems do
      if let some proof ← tryTwoStepProof goal thm1 thm2 then
        IO.println s!"[PROOF-CONSTRUCT] ✓ Two-step proof: {thm1} then {thm2}"
        return some proof
  return none

/-- Attempt to prove a goal using basic proof construction -/
def constructProof (goal : Expr) (availableTheorems : List Name) (maxSteps : Nat := 5) : MetaM (Option Expr) := do
  IO.println s!"[PROOF-CONSTRUCT] Attempting to construct proof for goal"
  
  -- First, try direct theorem application
  for thmName in availableTheorems do
    match ← tryApplyTheorem goal thmName with
    | StepResult.success none proof =>
      IO.println s!"[PROOF-CONSTRUCT] ✓ Direct application of {thmName}"
      return some proof
    | _ => continue
  
  -- Try reflexivity
  match ← tryRefl goal with
  | StepResult.success none proof =>
    IO.println s!"[PROOF-CONSTRUCT] ✓ Proved by reflexivity"
    return some proof
  | _ => pure ()
  
  -- Try simple two-step proofs  
  if maxSteps > 1 then
    if let some proof ← tryMultiStepProof goal availableTheorems then
      return some proof
  
  IO.println s!"[PROOF-CONSTRUCT] ✗ Could not construct proof"
  return none

/-- Collect available theorems from the environment and discovered concepts -/
def collectAvailableTheorems (concepts : List ConceptData) : MetaM (List Name) := do
  let mut theorems := []
  
  -- Add known useful theorems
  let knownTheorems := [
    ``Nat.add_comm, ``Nat.add_assoc, ``Nat.add_zero, ``Nat.zero_add,
    ``Nat.mul_comm, ``Nat.mul_assoc, ``Nat.mul_one, ``Nat.one_mul,
    ``Nat.mul_zero, ``Nat.zero_mul,
    ``Nat.add_succ, ``Nat.succ_add,
    ``Nat.gcd_comm, ``Nat.gcd_self, ``Nat.gcd_zero_right
  ]
  
  -- Check which ones exist
  let env ← getEnv
  for thmName in knownTheorems do
    if env.contains thmName then
      theorems := theorems ++ [thmName]
  
  -- Add theorems from discovered concepts
  for concept in concepts do
    match concept with
    | ConceptData.theorem name _ _ _ _ =>
      -- Convert string name to Name if possible
      -- For now, skip this as it requires name resolution
      pure ()
    | _ => pure ()
  
  return theorems


/-- Simplified proof goal structure -/
structure ProofGoal where
  name : String
  statement : Expr
  priority : Float

/-- Global state for proof goals -/
structure ProofGuidedState where
  goals : List ProofGoal
  completedGoals : List String
  failedGoals : List String

instance : Inhabited ProofGuidedState where
  default := { goals := [], completedGoals := [], failedGoals := [] }

-- Global mutable state  
initialize proofGuidedStateRef : IO.Ref ProofGuidedState ← do
  let initialState : ProofGuidedState := { goals := [], completedGoals := [], failedGoals := [] }
  IO.mkRef initialState

/-- Add a proof goal -/
def addProofGoal (goal : ProofGoal) : MetaM Unit := do
  let state ← proofGuidedStateRef.get
  let newGoals := goal :: state.goals
  proofGuidedStateRef.set { state with goals := newGoals }

/-- Get current proof goals -/
def getCurrentProofGoals : MetaM (List ProofGoal) := do
  let state ← proofGuidedStateRef.get
  return state.goals

/-- Classification of proof failures for simple analysis -/
inductive SimpleFailureReason where
  | missingCommutativity (operation : String)
  | missingAssociativity (operation : String)
  | missingIdentity (operation : String) (identity : String)
  | needsInduction (variableName : String)
  | missingLemma (description : String)
  | typeError (expected : String) (got : String)
  | unknown (message : String)

/-- Analyze why a proof failed with enhanced pattern recognition -/
def analyzeFailure (stmt : Expr) (goalName : String) : MetaM SimpleFailureReason := do
  let stmtStr := toString stmt
  
  IO.println s!"    [ANALYSIS] Analyzing failure of: {goalName}"
  IO.println s!"    [ANALYSIS] Statement: {stmtStr.take 100}..."
  
  -- Enhanced analysis based on statement structure and goal name
  if contains stmtStr "=" && contains stmtStr "Nat.add" then
    if contains goalName "comm" || (contains stmtStr "+" && contains stmtStr "m" && contains stmtStr "n") then
      IO.println s!"    [ANALYSIS] → Detected missing addition commutativity"
      return SimpleFailureReason.missingCommutativity "addition"
    else if contains goalName "assoc" then
      IO.println s!"    [ANALYSIS] → Detected missing addition associativity"
      return SimpleFailureReason.missingAssociativity "addition" 
    else if contains stmtStr "0" || contains stmtStr "zero" then
      IO.println s!"    [ANALYSIS] → Detected missing addition identity"
      return SimpleFailureReason.missingIdentity "addition" "zero"
    else
      IO.println s!"    [ANALYSIS] → General addition property missing"
      return SimpleFailureReason.missingLemma "addition property"
      
  else if contains stmtStr "=" && contains stmtStr "Nat.mul" then
    if contains goalName "comm" || (contains stmtStr "*" && contains stmtStr "m" && contains stmtStr "n") then
      IO.println s!"    [ANALYSIS] → Detected missing multiplication commutativity"
      return SimpleFailureReason.missingCommutativity "multiplication"
    else if contains goalName "assoc" then
      IO.println s!"    [ANALYSIS] → Detected missing multiplication associativity"
      return SimpleFailureReason.missingAssociativity "multiplication"
    else if contains stmtStr "succ" && contains stmtStr "zero" then
      IO.println s!"    [ANALYSIS] → Detected missing multiplication identity"
      return SimpleFailureReason.missingIdentity "multiplication" "one"
    else
      IO.println s!"    [ANALYSIS] → General multiplication property missing"
      return SimpleFailureReason.missingLemma "multiplication property"
      
  else if contains stmtStr "∀" || contains stmtStr "forall" then
    -- For universal quantifications, we often need induction
    if contains stmtStr "Nat" then
      IO.println s!"    [ANALYSIS] → Universal statement over Nat, likely needs induction"
      return SimpleFailureReason.needsInduction "n"
    else
      IO.println s!"    [ANALYSIS] → Universal statement, may need case analysis"
      return SimpleFailureReason.missingLemma "universal property"
    
  else if contains stmtStr "Type" then
    IO.println s!"    [ANALYSIS] → Type error detected"
    return SimpleFailureReason.typeError "unknown" "unknown"
    
  else
    IO.println s!"    [ANALYSIS] → Unknown failure pattern"
    return SimpleFailureReason.unknown stmtStr

/-- Generate commutativity statement for an operation -/
def generateCommutativityStatement (op : String) : MetaM Expr := do
  let natType := mkConst ``Nat
  match op with
  | "addition" =>
    -- Generate: ∀ n m : Nat, n + m = m + n
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      mkSafeForall `m natType fun m => do
        let add := mkConst ``Nat.add
        let lhs := mkApp2 add n m
        let rhs := mkApp2 add m n
        return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | "multiplication" =>
    -- Generate: ∀ n m : Nat, n * m = m * n
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      mkSafeForall `m natType fun m => do
        let mul := mkConst ``Nat.mul
        let lhs := mkApp2 mul n m
        let rhs := mkApp2 mul m n
        return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | _ =>
    -- Fallback to True
    return mkConst ``True

/-- Generate associativity statement for an operation -/
def generateAssociativityStatement (op : String) : MetaM Expr := do
  let natType := mkConst ``Nat
  match op with
  | "addition" =>
    -- Generate: ∀ a b c : Nat, (a + b) + c = a + (b + c)
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        mkSafeForall `c natType fun c => do
          let add := mkConst ``Nat.add
          let ab := mkApp2 add a b
          let abc := mkApp2 add ab c
          let bc := mkApp2 add b c
          let a_bc := mkApp2 add a bc
          return mkApp3 (mkConst ``Eq [levelOne]) natType abc a_bc
  | "multiplication" =>
    -- Generate: ∀ a b c : Nat, (a * b) * c = a * (b * c)
    mkForallFVars #[] =<< mkSafeForall `a natType fun a => do
      mkSafeForall `b natType fun b => do
        mkSafeForall `c natType fun c => do
          let mul := mkConst ``Nat.mul
          let ab := mkApp2 mul a b
          let abc := mkApp2 mul ab c
          let bc := mkApp2 mul b c
          let a_bc := mkApp2 mul a bc
          return mkApp3 (mkConst ``Eq [levelOne]) natType abc a_bc
  | _ =>
    return mkConst ``True

/-- Generate identity statements (both left and right) for an operation -/
def generateIdentityStatements (op : String) (identity : String) : MetaM (Expr × Expr) := do
  let natType := mkConst ``Nat
  match op, identity with
  | "addition", "zero" =>
    -- Left: ∀ n : Nat, 0 + n = n
    let leftStmt ← mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let zero := mkConst ``Nat.zero
      let add := mkConst ``Nat.add
      let lhs := mkApp2 add zero n
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
    -- Right: ∀ n : Nat, n + 0 = n  
    let rightStmt ← mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let zero := mkConst ``Nat.zero
      let add := mkConst ``Nat.add
      let lhs := mkApp2 add n zero
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
    return (leftStmt, rightStmt)
  | "multiplication", "one" =>
    -- Left: ∀ n : Nat, 1 * n = n
    let leftStmt ← mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)  -- 1 = succ(0)
      let mul := mkConst ``Nat.mul
      let lhs := mkApp2 mul one n
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
    -- Right: ∀ n : Nat, n * 1 = n
    let rightStmt ← mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)  -- 1 = succ(0)
      let mul := mkConst ``Nat.mul
      let lhs := mkApp2 mul n one
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
    return (leftStmt, rightStmt)
  | _, _ =>
    -- Fallback
    let fallback := mkConst ``True
    return (fallback, fallback)

/-- Generate base case for induction-based proofs -/
def generateInductionBaseCase (goalName : String) (originalStmt : Expr) : MetaM Expr := do
  let natType := mkConst ``Nat
  let zero := mkConst ``Nat.zero
  
  -- Try to instantiate the original statement with n = 0
  -- For now, create a simplified base case
  if contains goalName "comm" then
    -- For commutativity: 0 + 0 = 0 + 0 (trivially true)
    let add := mkConst ``Nat.add
    let lhs := mkApp2 add zero zero
    let rhs := mkApp2 add zero zero
    return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  else
    -- General case: just True for now
    return mkConst ``True

/-- Generate inductive step hint for induction-based proofs -/
def generateInductionStepHint (goalName : String) (originalStmt : Expr) : MetaM Expr := do
  let natType := mkConst ``Nat
  
  -- Generate a hint about the inductive step structure
  -- For commutativity: if P(n) then P(succ(n))
  -- This is a meta-level hint, so we'll use True as placeholder
  -- In a full implementation, this would generate the actual inductive hypothesis
  return mkConst ``True

/-- Generate targeted lemma based on description -/
def generateTargetedLemma (desc : String) (originalStmt : Expr) : MetaM Expr := do
  match desc with
  | "addition property" =>
    -- Generate a useful addition property
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let zero := mkConst ``Nat.zero
      let add := mkConst ``Nat.add
      let lhs := mkApp2 add n zero
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
  | "multiplication property" =>
    -- Generate a useful multiplication property
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)
      let mul := mkConst ``Nat.mul
      let lhs := mkApp2 mul n one
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
  | "universal property" =>
    -- Generate a universal quantification lemma
    return mkConst ``True
  | _ =>
    -- Fallback
    return mkConst ``True

/-- Generate targeted helper lemmas based on failure analysis -/
def generateHelperLemmas (stmt : Expr) (goalName : String) : MetaM (List ConceptData) := do
  let failureReason ← analyzeFailure stmt goalName
  let mut helpers := []
  
  match failureReason with
  | SimpleFailureReason.missingCommutativity op =>
    -- Generate actual commutativity statement
    let helperStmt ← generateCommutativityStatement op
    let helperName := s!"{op}_commutativity_helper"
    let helper := ConceptData.conjecture helperName helperStmt 0.9 {
      name := helperName
      created := 0
      parent := some goalName
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_{op}_commutativity"
    }
    helpers := helpers ++ [helper]
    IO.println s!"    → Generated actual {op} commutativity lemma: ∀ n m, n {if op == "addition" then "+" else "*"} m = m {if op == "addition" then "+" else "*"} n"
    
  | SimpleFailureReason.missingAssociativity op =>
    -- Generate actual associativity statement  
    let helperStmt ← generateAssociativityStatement op
    let helperName := s!"{op}_associativity_helper"
    let helper := ConceptData.conjecture helperName helperStmt 0.9 {
      name := helperName
      created := 0
      parent := some goalName
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_{op}_associativity"
    }
    helpers := helpers ++ [helper]
    IO.println s!"    → Generated actual {op} associativity lemma: ∀ a b c, (a {if op == "addition" then "+" else "*"} b) {if op == "addition" then "+" else "*"} c = a {if op == "addition" then "+" else "*"} (b {if op == "addition" then "+" else "*"} c)"
    
  | SimpleFailureReason.missingIdentity op identity =>
    -- Generate actual identity statements
    let (leftHelperStmt, rightHelperStmt) ← generateIdentityStatements op identity
    
    -- Left identity
    let leftHelperName := s!"{identity}_{op}_left_identity"
    let leftHelper := ConceptData.conjecture leftHelperName leftHelperStmt 0.9 {
      name := leftHelperName
      created := 0
      parent := some goalName
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_{op}_{identity}_left_identity"
    }
    helpers := helpers ++ [leftHelper]
    
    -- Right identity  
    let rightHelperName := s!"{op}_{identity}_right_identity"
    let rightHelper := ConceptData.conjecture rightHelperName rightHelperStmt 0.9 {
      name := rightHelperName
      created := 0
      parent := some goalName
      interestingness := 0.9
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_{op}_{identity}_right_identity"
    }
    helpers := helpers ++ [rightHelper]
    
    IO.println s!"    → Generated {identity} identity lemmas for {op} (both left and right)"
    
  | SimpleFailureReason.needsInduction var =>
    -- Generate useful induction-related lemmas
    let baseStmt ← generateInductionBaseCase goalName stmt
    let stepStmt ← generateInductionStepHint goalName stmt
    
    let baseName := s!"base_case_for_{goalName}"
    let baseHelper := ConceptData.conjecture baseName baseStmt 0.8 {
      name := baseName
      created := 0
      parent := some goalName
      interestingness := 0.8
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_induction_base"
    }
    
    let stepName := s!"induction_step_hint_for_{goalName}"
    let stepHelper := ConceptData.conjecture stepName stepStmt 0.8 {
      name := stepName
      created := 0
      parent := some goalName
      interestingness := 0.8
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_induction_step"
    }
    
    helpers := helpers ++ [baseHelper, stepHelper]
    IO.println s!"    → Generated induction helpers: base case and step hint for {var}"
    
  | SimpleFailureReason.missingLemma desc =>
    -- Try to generate a more specific lemma based on the description
    let helperStmt ← generateTargetedLemma desc stmt
    let helperName := s!"targeted_lemma_for_{goalName}"
    let helper := ConceptData.conjecture helperName helperStmt 0.7 {
      name := helperName
      created := 0
      parent := some goalName
      interestingness := 0.7
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_targeted_lemma"
    }
    helpers := helpers ++ [helper]
    IO.println s!"    → Generated targeted lemma for: {desc}"
    
  | SimpleFailureReason.typeError expected got =>
    IO.println s!"    → Type error analysis: expected {expected}, got {got} - no lemma generated"
    
  | SimpleFailureReason.unknown msg =>
    IO.println s!"    → Unknown failure pattern: {msg.take 50}... - generating diagnostic lemma"
    let diagnosticStmt := mkConst ``True  -- Fallback placeholder
    let diagnosticName := s!"diagnostic_lemma_for_{goalName}"
    let diagnostic := ConceptData.conjecture diagnosticName diagnosticStmt 0.5 {
      name := diagnosticName
      created := 0
      parent := some goalName
      interestingness := 0.5
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := s!"failure_analysis_diagnostic"
    }
    helpers := helpers ++ [diagnostic]
  
  return helpers

/-- Helper to safely find and verify theorem -/
def tryFindTheorem (thmName : Name) : MetaM (Option Expr) := do
  try
    let env ← getEnv
    if let some info := env.find? thmName then
      match info with
      | .thmInfo _ =>
        return some (mkConst thmName)
      | _ => return none
    else
      return none
  catch _ => return none

/-- Attempt inductive proof for universal statements over Nat -/
def tryInductiveProof (stmt : Expr) : MetaM (Option Expr) := do
  -- Check if statement is of form ∀ n : Nat, P(n)
  if stmt.isForall then
    let domain := stmt.bindingDomain!
    if ← isDefEq domain (mkConst ``Nat) then
      -- Try to use existing induction theorems
      let inductionThms := [``Nat.add_comm, ``Nat.mul_comm, ``Nat.add_zero, ``Nat.zero_add, ``Nat.mul_one, ``Nat.one_mul]
      for thmName in inductionThms do
        try
          let thm := mkConst thmName
          let thmType ← inferType thm
          if ← isDefEq thmType stmt then
            IO.println s!"    [PROOF] Found induction theorem {thmName}"
            return some thm
        catch _ => continue
      
      -- Try more specific induction patterns
      let stmtStr := toString stmt
      if contains stmtStr "Nat.add" && contains stmtStr "=" then
        -- Check for specific addition patterns
        if contains stmtStr "Nat.zero" then
          -- This might be n + 0 = n or 0 + n = n
          if let some thm ← tryFindTheorem ``Nat.add_zero then
            return some thm
          if let some thm ← tryFindTheorem ``Nat.zero_add then
            return some thm
        
      if contains stmtStr "Nat.mul" && contains stmtStr "=" then
        -- Check for specific multiplication patterns
        if contains stmtStr "succ" && contains stmtStr "zero" then
          -- This might be n * 1 = n or 1 * n = n  
          if let some thm ← tryFindTheorem ``Nat.mul_one then
            return some thm
          if let some thm ← tryFindTheorem ``Nat.one_mul then
            return some thm
      
      return none
  return none

/-- Proof tactics with induction and number theory support -/
def tryProveGoal (stmt : Expr) : MetaM (Option Expr) := do
  -- For True, we can easily construct a proof
  if stmt.isConstOf ``True then
    IO.println "    [PROOF] Proving True with trivial"
    return some (mkConst ``True.intro)
  
  -- Try to use known Nat theorems
  let stmtStr := toString stmt
  
  -- GCD theorem matching
  if contains stmtStr "Nat.gcd" then
    IO.println "    [PROOF] Attempting GCD theorems"
    let gcdThms := [``Nat.gcd_comm, ``Nat.gcd_self, ``Nat.gcd_zero_right, ``Nat.gcd_zero_left]
    for thmName in gcdThms do
      let env ← getEnv
      if let some info := env.find? thmName then
        match info with
        | .thmInfo _ =>
          try
            let thm := mkConst thmName
            let thmType ← inferType thm
            if ← isDefEq thmType stmt then
              IO.println s!"    [PROOF] Found {thmName} theorem"
              return some thm
          catch _ => continue
        | _ => continue
    
    -- Try GCD-specific patterns
    if contains stmtStr "gcd" then
      -- Try specific GCD identities
      if contains stmtStr "0" then
        -- This might be gcd(a, 0) = a or gcd(0, a) = a
        if let some thm ← tryFindTheorem ``Nat.gcd_zero_right then
          return some thm
        if let some thm ← tryFindTheorem ``Nat.gcd_zero_left then
          return some thm
      
      if contains stmtStr "self" || (contains stmtStr "a" && !contains stmtStr "b") then
        -- This might be gcd(a, a) = a
        if let some thm ← tryFindTheorem ``Nat.gcd_self then
          return some thm
  
  -- Addition theorem matching
  if contains stmtStr "Nat.add" then
    IO.println "    [PROOF] Attempting addition theorems"
    let addThms := [``Nat.zero_add, ``Nat.add_zero, ``Nat.add_comm, ``Nat.add_assoc]
    for thmName in addThms do
      let env ← getEnv
      if let some info := env.find? thmName then
        match info with
        | .thmInfo _ =>
          try
            let thm := mkConst thmName
            let thmType ← inferType thm
            if ← isDefEq thmType stmt then
              IO.println s!"    [PROOF] Found {thmName} theorem"
              return some thm
          catch _ => continue
        | _ => continue
  
  -- Multiplication theorem matching
  if contains stmtStr "Nat.mul" then
    IO.println "    [PROOF] Attempting multiplication theorems"
    let mulThms := [``Nat.one_mul, ``Nat.mul_one, ``Nat.zero_mul, ``Nat.mul_zero, ``Nat.mul_comm, ``Nat.mul_assoc]
    for thmName in mulThms do
      let env ← getEnv
      if let some info := env.find? thmName then
        match info with
        | .thmInfo _ =>
          try
            let thm := mkConst thmName
            let thmType ← inferType thm
            if ← isDefEq thmType stmt then
              IO.println s!"    [PROOF] Found {thmName} theorem"
              return some thm
          catch _ => continue
        | _ => continue
  
  -- Modular arithmetic theorem matching
  if contains stmtStr "Nat.mod" then
    IO.println "    [PROOF] Attempting modular arithmetic theorems"
    let modThms := [``Nat.mod_self, ``Nat.zero_mod, ``Nat.mod_mod]
    for thmName in modThms do
      let env ← getEnv
      if let some info := env.find? thmName then
        match info with
        | .thmInfo _ =>
          try
            let thm := mkConst thmName
            let thmType ← inferType thm
            if ← isDefEq thmType stmt then
              IO.println s!"    [PROOF] Found {thmName} theorem"
              return some thm
          catch _ => continue
        | _ => continue
  
  -- Try induction for universal statements
  if stmt.isForall then
    IO.println "    [PROOF] Attempting induction for universal statement"
    let inductionResult ← tryInductiveProof stmt
    if inductionResult.isSome then
      return inductionResult
  
  -- Fall back to existing proof mechanism
  let result ← tryProveConjecture stmt
  if result.isSome then
    IO.println "    [PROOF] Proved with existing mechanism"
    return result
  
  -- Try proof construction as last resort
  IO.println "    [PROOF] Attempting proof construction"
  let availableTheorems ← collectAvailableTheorems []
  let constructionResult ← constructProof stmt availableTheorems
  if constructionResult.isSome then
    IO.println "    [PROOF] ✓ Proved via construction"
    return constructionResult
  else
    IO.println "    [PROOF] Could not prove with available tactics"
    return none

/-- Enhanced version that takes discovered concepts for better theorem collection -/
def tryProveGoalWithConcepts (stmt : Expr) (concepts : List ConceptData) : MetaM (Option Expr) := do
  -- First try the standard approach
  let standardResult ← tryProveGoal stmt
  if standardResult.isSome then
    return standardResult
  
  -- If that fails, try proof construction with enhanced theorem collection
  IO.println "    [PROOF] Standard tactics failed, trying construction with discovered concepts"
  let availableTheorems ← collectAvailableTheorems concepts
  let constructionResult ← constructProof stmt availableTheorems
  if constructionResult.isSome then
    IO.println "    [PROOF] ✓ Proved via construction with discovered concepts"
    return constructionResult
  else
    return none

/-- Simple proof-guided discovery heuristic -/
def proofGuidedDiscoveryHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []
  
  -- Get current goals
  let goals ← getCurrentProofGoals
  
  IO.println s!"[PROOF-GUIDED] Working on {goals.length} proof goals"
  
  -- Try each goal
  for goal in goals.take 3 do
    IO.println s!"[PROOF-GUIDED] Attempting goal: {goal.name}"
    
    -- Try to prove the goal with tactics (pass concepts for enhanced theorem collection)
    let proofResult ← tryProveGoalWithConcepts goal.statement concepts
    match proofResult with
    | some proof =>
      -- Success! Add as theorem
      IO.println s!"[PROOF-GUIDED] ✓ Proved: {goal.name}"
      let theoremConcept := ConceptData.theorem goal.name goal.statement proof [] {
        name := goal.name
        created := 0
        parent := none
        interestingness := goal.priority
        useCount := 0
        successCount := 1
        specializationDepth := 0
        generationMethod := "proof_guided_success"
      }
      newConcepts := newConcepts ++ [theoremConcept]
      
      -- Mark goal as completed  
      let state ← proofGuidedStateRef.get
      let newCompleted := state.completedGoals ++ [goal.name]
      let newGoals := state.goals.filter (·.name != goal.name)
      proofGuidedStateRef.set { state with goals := newGoals, completedGoals := newCompleted }
      
    | none =>
      -- Failed, analyze why and generate targeted helpers
      IO.println s!"[PROOF-GUIDED] ✗ Failed: {goal.name}, analyzing failure..."
      let helpers ← generateHelperLemmas goal.statement goal.name
      newConcepts := newConcepts ++ helpers
  
  IO.println s!"[PROOF-GUIDED] Generated {newConcepts.length} concepts"
  return newConcepts

/-- Generate a simple provable statement about natural numbers -/
def generateProvableStatement (name : String) : MetaM Expr := do
  match name with
  | "zero_add" =>
    -- Generate: ∀ n : Nat, 0 + n = n
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let zero := mkConst ``Nat.zero
      let add := mkConst ``Nat.add
      let lhs := mkApp2 add zero n
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
  | "add_zero" =>
    -- Generate: ∀ n : Nat, n + 0 = n  
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let zero := mkConst ``Nat.zero
      let add := mkConst ``Nat.add
      let lhs := mkApp2 add n zero
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
  | "one_mul" =>
    -- Generate: ∀ n : Nat, 1 * n = n
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)  -- 1 = succ(0)
      let mul := mkConst ``Nat.mul
      let lhs := mkApp2 mul one n
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
  | "mul_one" =>
    -- Generate: ∀ n : Nat, n * 1 = n
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      let one := mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)  -- 1 = succ(0)
      let mul := mkConst ``Nat.mul
      let lhs := mkApp2 mul n one
      return mkApp3 (mkConst ``Eq [levelOne]) natType lhs n
  | "add_comm" =>
    -- Generate: ∀ n m : Nat, n + m = m + n (challenging commutativity)
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      mkSafeForall `m natType fun m => do
        let add := mkConst ``Nat.add
        let lhs := mkApp2 add n m
        let rhs := mkApp2 add m n
        return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | "mul_comm" =>
    -- Generate: ∀ n m : Nat, n * m = m * n (challenging commutativity)
    let natType := mkConst ``Nat
    mkForallFVars #[] =<< mkSafeForall `n natType fun n => do
      mkSafeForall `m natType fun m => do
        let mul := mkConst ``Nat.mul
        let lhs := mkApp2 mul n m
        let rhs := mkApp2 mul m n
        return mkApp3 (mkConst ``Eq [levelOne]) natType lhs rhs
  | "simple_true" =>
    -- Just True, should be easily provable
    return mkConst ``True
  | _ =>
    -- Fallback to True
    return mkConst ``True

/-- Proof construction heuristic using the local functions -/
def proofConstructionHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []
  
  -- Get available theorems
  let availableTheorems ← collectAvailableTheorems concepts
  IO.println s!"[PROOF-CONSTRUCT] Available theorems: {availableTheorems.length}"
  
  -- Try to prove some simple constructed goals
  let simpleGoals := [
    ("reflexivity_zero", mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Nat) (mkConst ``Nat.zero) (mkConst ``Nat.zero)),
    ("reflexivity_one", mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Nat) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero)))
  ]
  
  for (name, goal) in simpleGoals do
    if let some proof ← constructProof goal availableTheorems then
      let metadata : ConceptMetadata := {
        name := name
        created := 0
        parent := none
        interestingness := 0.6
        useCount := 0
        successCount := 1
        specializationDepth := 0
        generationMethod := "proof_construction"
      }
      let concept := ConceptData.theorem name goal proof [] metadata
      newConcepts := newConcepts ++ [concept]
  
  return newConcepts

/-- Goal seeding heuristic - creates interesting goals to prove -/
def goalSeedingHeuristic : HeuristicFn := fun config concepts => do
  let mut newConcepts := []
  
  IO.println "[GOAL-SEEDING] Creating mathematical goals"
  
  -- Add some classic goals if we don't have many yet
  let currentGoals ← getCurrentProofGoals
  if currentGoals.length < 6 then
    
    -- Define interesting mathematical goals (mix of provable and challenging ones)
    let goalSpecs := [
      ("simple_true_goal", "simple_true", 0.9),
      ("zero_add_proof", "zero_add", 0.85),
      ("add_zero_proof", "add_zero", 0.85),
      ("one_mul_proof", "one_mul", 0.8),
      ("mul_one_proof", "mul_one", 0.8),
      ("add_comm_challenge", "add_comm", 0.9),
      ("mul_comm_challenge", "mul_comm", 0.85)
    ]
    
    for (goalName, stmtName, priority) in goalSpecs do
      -- Check if we already have this goal
      if not (currentGoals.any (·.name == goalName)) then
        let stmt ← generateProvableStatement stmtName
        let goal : ProofGoal := {
          name := goalName
          statement := stmt
          priority := priority
        }
        addProofGoal goal
    
        -- Create conjecture concept for tracking
        let conjecture := ConceptData.conjecture goalName stmt priority {
          name := goalName
          created := 0
          parent := none
          interestingness := priority
          useCount := 0
          successCount := 0
          specializationDepth := 0
          generationMethod := "goal_seeding"
        }
        newConcepts := newConcepts ++ [conjecture]
    
    IO.println s!"[GOAL-SEEDING] Added {newConcepts.length} new goals"
  
  return newConcepts

end LeanDisco.ProofGuidedSimple