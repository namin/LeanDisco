import Lean
import LeanDisco.Basic

set_option maxHeartbeats 1000000000

open Lean Elab Term Meta
open LeanDisco

/-- Test computable benchmark statements -/
def testComputable : TermElabM Unit := do
  IO.println "=== Testing Computable Benchmark Statements ==="
  
  let kb : KnowledgeBase := { 
    concepts := [], 
    heuristics := { entries := [] },
    recentConcepts := [],
    evaluators := { entries := [] },
    config := {},
    iteration := 0,
    history := []
  }
  
  -- Test the GCD case with actual numbers (20! = 2432902008176640000)
  IO.println "Testing: Nat.gcd 2432902008176640000 200000 = 40000"
  let gcdStmt ← elabTerm (← `(Nat.gcd 2432902008176640000 200000 = 40000)) none
  let gcdProof ← tryProveConjecture gcdStmt kb
  match gcdProof with
  | some _ => IO.println "✓ SUCCESS: GCD statement proved!"
  | none => IO.println "✗ FAILED: GCD statement not proved"
  
  -- Test a simple arithmetic case
  IO.println "Testing: 2 + 3 = 5"
  let arithStmt ← elabTerm (← `(2 + 3 = 5)) none  
  let arithProof ← tryProveConjecture arithStmt kb
  match arithProof with
  | some _ => IO.println "✓ SUCCESS: Arithmetic proved!"
  | none => IO.println "✗ FAILED: Arithmetic not proved"
  
  -- Test another computable case  
  IO.println "Testing: 100 % 7 = 2"
  let modStmt ← elabTerm (← `(100 % 7 = 2)) none
  let modProof ← tryProveConjecture modStmt kb
  match modProof with
  | some _ => IO.println "✓ SUCCESS: Modulo proved!"
  | none => IO.println "✗ FAILED: Modulo not proved"
  
  -- Debug: check what the GCD actually reduces to
  IO.println "\n=== Debug: Reduction Analysis ==="
  let gcdExpr ← elabTerm (← `(Nat.gcd 2432902008176640000 200000)) none
  let gcdReduced ← reduce gcdExpr
  IO.println s!"Nat.gcd 2432902008176640000 200000 reduces to: {gcdReduced}"
  
  let forty ← elabTerm (← `(40000)) none
  let fortyReduced ← reduce forty
  IO.println s!"40000 reduces to: {fortyReduced}"
  
  let areEqual ← isDefEq gcdReduced fortyReduced
  IO.println s!"Are they definitionally equal? {areEqual}"

/-- Run the test -/
#eval testComputable