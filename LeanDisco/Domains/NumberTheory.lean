import LeanDisco.Basic
import LeanDisco.IncrementalSave
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.PrimeCounting

set_option linter.unusedVariables false

namespace LeanDisco.Domains.NumberTheory

open Lean Meta Elab
open LeanDisco.IncrementalSave

/-- Configuration specific to number theory mining -/
structure NumberTheoryConfig where
  includeBasicArithmetic : Bool := true
  includeDivisibility : Bool := true
  includePrimeTheory : Bool := true
  includeModularArithmetic : Bool := true
  includeSequences : Bool := true
  includeDiophantine : Bool := false
  maxNumber : Nat := 100

/-- Mine number theory concepts based on configuration -/
def mineNumberTheoryConcepts (config : NumberTheoryConfig) : MetaM (List ConceptData) := do
  let env ← getEnv
  let mut concepts : List ConceptData := []

  let mkMeta (name : String) (method : String) : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := s!"mined_{method}"
  }

  -- Basic arithmetic properties
  if config.includeBasicArithmetic then
    let basicTheorems : List (String × String) := [
      ("add_assoc", "∀ a b c : ℕ, (a + b) + c = a + (b + c)"),
      ("add_comm", "∀ a b : ℕ, a + b = b + a"),
      ("add_zero", "∀ a : ℕ, a + 0 = a"),
      ("zero_add", "∀ a : ℕ, 0 + a = a"),
      ("mul_assoc", "∀ a b c : ℕ, (a * b) * c = a * (b * c)"),
      ("mul_comm", "∀ a b : ℕ, a * b = b * a"),
      ("mul_one", "∀ a : ℕ, a * 1 = a"),
      ("one_mul", "∀ a : ℕ, 1 * a = a"),
      ("mul_zero", "∀ a : ℕ, a * 0 = 0"),
      ("zero_mul", "∀ a : ℕ, 0 * a = 0"),
      ("left_distrib", "∀ a b c : ℕ, a * (b + c) = a * b + a * c"),
      ("right_distrib", "∀ a b c : ℕ, (a + b) * c = a * c + b * c")
    ]

    for (thmName, _description) in basicTheorems do
      let possibleNames : List Name := [
        Name.mkStr2 "Nat" thmName,
        Name.mkStr1 thmName
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              thmName
              val.type
              (mkConst name)
              []
              (mkMeta thmName "arithmetic")]
            break
          | _ => continue

  -- Divisibility theory
  if config.includeDivisibility then
    let divTheorems : List (String × String) := [
      ("dvd_refl", "∀ a : ℕ, a ∣ a"),
      ("dvd_trans", "∀ a b c : ℕ, a ∣ b → b ∣ c → a ∣ c"),
      ("dvd_add", "∀ a b c : ℕ, a ∣ b → a ∣ c → a ∣ (b + c)"),
      ("dvd_mul", "∀ a b c : ℕ, a ∣ b → a ∣ (b * c)"),
      ("gcd_comm", "∀ a b : ℕ, gcd a b = gcd b a"),
      ("gcd_assoc", "∀ a b c : ℕ, gcd (gcd a b) c = gcd a (gcd b c)"),
      ("gcd_zero_left", "∀ a : ℕ, gcd 0 a = a"),
      ("gcd_zero_right", "∀ a : ℕ, gcd a 0 = a"),
      ("lcm_comm", "∀ a b : ℕ, lcm a b = lcm b a"),
      ("lcm_assoc", "∀ a b c : ℕ, lcm (lcm a b) c = lcm a (lcm b c)")
    ]

    for (thmName, _description) in divTheorems do
      let possibleNames : List Name := [
        Name.mkStr2 "Nat" thmName,
        Name.mkStr1 thmName
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              thmName
              val.type
              (mkConst name)
              []
              (mkMeta thmName "divisibility")]
            break
          | _ => continue

  -- Prime number theory
  if config.includePrimeTheory then
    let primeTheorems : List (String × String) := [
      ("prime_def", "∀ p : ℕ, Prime p ↔ p > 1 ∧ ∀ a : ℕ, a ∣ p → a = 1 ∨ a = p"),
      ("prime_two", "Prime 2"),
      ("prime_three", "Prime 3"),
      ("prime_five", "Prime 5"),
      ("prime_seven", "Prime 7"),
      ("prime_dvd_mul", "∀ p a b : ℕ, Prime p → p ∣ a * b → p ∣ a ∨ p ∣ b"),
      ("infinite_primes", "∀ n : ℕ, ∃ p : ℕ, p > n ∧ Prime p")
    ]

    for (thmName, _description) in primeTheorems do
      let possibleNames : List Name := [
        Name.mkStr2 "Nat" thmName,
        Name.mkStr1 thmName,
        Name.mkStr2 "Prime" thmName
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              thmName
              val.type
              (mkConst name)
              []
              (mkMeta thmName "prime")]
            break
          | _ => continue

  -- Modular arithmetic
  if config.includeModularArithmetic then
    let modTheorems : List (String × String) := [
      ("mod_mod", "∀ a n : ℕ, a % n % n = a % n"),
      ("add_mod", "∀ a b n : ℕ, (a + b) % n = (a % n + b % n) % n"),
      ("mul_mod", "∀ a b n : ℕ, (a * b) % n = (a % n * b % n) % n"),
      ("mod_eq_mod_iff_mod_sub", "∀ a b n : ℕ, a % n = b % n ↔ n ∣ (a - b)"),
      ("mod_two_eq_zero_or_one", "∀ a : ℕ, a % 2 = 0 ∨ a % 2 = 1")
    ]

    for (thmName, _description) in modTheorems do
      let possibleNames : List Name := [
        Name.mkStr2 "Nat" thmName,
        Name.mkStr1 thmName
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              thmName
              val.type
              (mkConst name)
              []
              (mkMeta thmName "modular")]
            break
          | _ => continue

  -- Number sequences
  if config.includeSequences then
    let seqTheorems : List (String × String) := [
      ("fib_zero", "fib 0 = 0"),
      ("fib_one", "fib 1 = 1"),
      ("fib_succ_succ", "∀ n : ℕ, fib (n + 2) = fib n + fib (n + 1)"),
      ("fib_add", "∀ m n : ℕ, fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)")
    ]

    for (thmName, _description) in seqTheorems do
      let possibleNames : List Name := [
        Name.mkStr2 "Nat" thmName,
        Name.mkStr1 thmName
      ]

      for name in possibleNames do
        if let some info := env.find? name then
          match info with
          | .thmInfo val =>
            concepts := concepts ++ [ConceptData.theorem
              thmName
              val.type
              (mkConst name)
              []
              (mkMeta thmName "sequence")]
            break
          | _ => continue

  -- Generate specific numbers as concepts
  for i in [0:config.maxNumber] do
    let natLit := mkNatLit i
    concepts := concepts ++ [
      ConceptData.definition s!"nat_{i}" (mkConst ``Nat) natLit none [] (mkMeta s!"nat_{i}" "concrete")
    ]

  -- Generate small primes as special concepts
  let smallPrimes := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
  for p in smallPrimes do
    if p ≤ config.maxNumber then
      concepts := concepts ++ [
        ConceptData.definition s!"prime_{p}" (mkConst ``Nat) (mkNatLit p) none [] (mkMeta s!"prime_{p}" "prime_concrete")
      ]

  return concepts

/-- Generate number theory concepts with specific operations -/
def generateNumberTheoryOperations (config : NumberTheoryConfig) : MetaM (List ConceptData) := do
  let mut concepts : List ConceptData := []

  let mkMeta (name : String) (method : String) : ConceptMetadata := {
    name := name
    created := 0
    parent := none
    interestingness := 1.0
    useCount := 0
    successCount := 0
    specializationDepth := 0
    generationMethod := method
  }

  -- Basic operations
  let natToNatToNat ← mkArrow (mkConst ``Nat) (← mkArrow (mkConst ``Nat) (mkConst ``Nat))

  concepts := concepts ++ [
    ConceptData.definition "add" natToNatToNat (mkConst ``Nat.add) none [] (mkMeta "add" "operation"),
    ConceptData.definition "mul" natToNatToNat (mkConst ``Nat.mul) none [] (mkMeta "mul" "operation"),
    ConceptData.definition "sub" natToNatToNat (mkConst ``Nat.sub) none [] (mkMeta "sub" "operation"),
    ConceptData.definition "mod" natToNatToNat (mkConst ``Nat.mod) none [] (mkMeta "mod" "operation"),
    ConceptData.definition "gcd" natToNatToNat (mkConst ``Nat.gcd) none [] (mkMeta "gcd" "operation"),
    ConceptData.definition "lcm" natToNatToNat (mkConst ``Nat.lcm) none [] (mkMeta "lcm" "operation")
  ]

  -- Predicates will be added later

  return concepts

/-- Run complete number theory discovery -/
def runNumberTheoryDiscovery (domainConfig : NumberTheoryConfig) (discoveryConfig : DiscoveryConfig) (maxIterations : Nat) : MetaM Unit := do
  let initialConcepts ← mineNumberTheoryConcepts domainConfig
  let operations ← generateNumberTheoryOperations domainConfig
  let seedConcepts := initialConcepts ++ operations

  let _ ← runDiscoveryCustomWithSaving "numbertheory_discovery" seedConcepts [] [] maxIterations false discoveryConfig "log/numbertheory_discovery"

end LeanDisco.Domains.NumberTheory
