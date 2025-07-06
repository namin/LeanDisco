import Lean
import Lean.Meta.Basic
import Lean.Elab.Command

import LeanDisco.Types
import LeanDisco.Basic
import LeanDisco.IncrementalSave

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Meta Elab
open LeanDisco.IncrementalSave

namespace LeanDisco.Domains.Lists

/-
# Lists Domain - Perfect for Inductive Discovery

Lists are the ideal structure for demonstrating inductive reasoning because:
1. They are defined inductively (nil and cons)
2. All list operations are naturally recursive
3. Most theorems about lists require induction to prove
4. Many patterns emerge that generalize across different list functions

This domain will showcase how the induction heuristic can discover:
- General theorems about list length, append, reverse, etc.
- Relationships between different list operations
- Properties that hold for all lists (universal quantification)
-/

-- Core list operations and properties for discovery

def listNil : List Nat := []

def listSingle (n : Nat) : List Nat := [n]

def listPair (n m : Nat) : List Nat := [n, m]

def listTriple (n m k : Nat) : List Nat := [n, m, k]

-- Some basic concrete lists for discovery
def list_0 : List Nat := [0]
def list_1 : List Nat := [1] 
def list_01 : List Nat := [0, 1]
def list_10 : List Nat := [1, 0]
def list_012 : List Nat := [0, 1, 2]
def list_210 : List Nat := [2, 1, 0]

-- Helper function to create lists of consecutive numbers
def range_list (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | Nat.succ k => range_list k ++ [k]

-- List operations that will generate inductive patterns
def list_append_empty_left (l : List Nat) : List Nat := [] ++ l
def list_append_empty_right (l : List Nat) : List Nat := l ++ []
def list_append_single_left (n : Nat) (l : List Nat) : List Nat := [n] ++ l
def list_append_single_right (l : List Nat) (n : Nat) : List Nat := l ++ [n]

-- Length operations that create inductive patterns
def length_nil : Nat := List.length ([] : List Nat)
def length_single (n : Nat) : Nat := List.length [n]
def length_pair (n m : Nat) : Nat := List.length [n, m]
def length_triple (n m k : Nat) : Nat := List.length [n, m, k]

-- Head and tail operations
def head_default_nil : Nat := List.headD ([] : List Nat) 0
def head_default_single (n : Nat) : Nat := List.headD [n] 0
def head_default_pair (n m : Nat) : Nat := List.headD [n, m] 0

def tail_nil : List Nat := List.tail ([] : List Nat)
def tail_single (n : Nat) : List Nat := List.tail [n]
def tail_pair (n m : Nat) : List Nat := List.tail [n, m]

-- Reverse operations
def reverse_nil : List Nat := List.reverse ([] : List Nat)
def reverse_single (n : Nat) : List Nat := List.reverse [n]
def reverse_pair (n m : Nat) : List Nat := List.reverse [n, m]
def reverse_triple (n m k : Nat) : List Nat := List.reverse [n, m, k]

-- Map operations with simple functions
def map_succ_nil : List Nat := List.map Nat.succ ([] : List Nat)
def map_succ_single (n : Nat) : List Nat := List.map Nat.succ [n]
def map_succ_pair (n m : Nat) : List Nat := List.map Nat.succ [n, m]

def map_double_nil : List Nat := List.map (fun x => x + x) ([] : List Nat)
def map_double_single (n : Nat) : List Nat := List.map (fun x => x + x) [n]
def map_double_pair (n m : Nat) : List Nat := List.map (fun x => x + x) [n, m]

-- Fold operations
def fold_add_nil : Nat := List.foldl (· + ·) 0 ([] : List Nat)
def fold_add_single (n : Nat) : Nat := List.foldl (· + ·) 0 [n]
def fold_add_pair (n m : Nat) : Nat := List.foldl (· + ·) 0 [n, m]
def fold_add_triple (n m k : Nat) : Nat := List.foldl (· + ·) 0 [n, m, k]

def fold_mul_nil : Nat := List.foldl (· * ·) 1 ([] : List Nat)
def fold_mul_single (n : Nat) : Nat := List.foldl (· * ·) 1 [n]
def fold_mul_pair (n m : Nat) : Nat := List.foldl (· * ·) 1 [n, m]

-- Filter operations
def filter_even_nil : List Nat := List.filter (fun x => x % 2 = 0) ([] : List Nat)
def filter_even_single_0 : List Nat := List.filter (fun x => x % 2 = 0) [0]
def filter_even_single_1 : List Nat := List.filter (fun x => x % 2 = 0) [1]
def filter_even_pair_01 : List Nat := List.filter (fun x => x % 2 = 0) [0, 1]
def filter_even_pair_02 : List Nat := List.filter (fun x => x % 2 = 0) [0, 2]

-- Key theorems that should be discovered through induction
-- These are the "target" theorems that demonstrate inductive patterns
-- For now, we'll create simple examples rather than full proofs

-- Example specific instances that should lead to general inductive theorems
def length_append_example_1 : Nat := List.length ([1] ++ [2]) -- should equal 2
def length_append_example_2 : Nat := List.length ([1, 2] ++ [3]) -- should equal 3
def length_append_example_3 : Nat := List.length ([] ++ [1, 2]) -- should equal 2

def reverse_reverse_example_1 : List Nat := List.reverse (List.reverse [1]) -- should equal [1]
def reverse_reverse_example_2 : List Nat := List.reverse (List.reverse [1, 2]) -- should equal [1, 2]
def reverse_reverse_example_3 : List Nat := List.reverse (List.reverse [1, 2, 3]) -- should equal [1, 2, 3]

def map_append_example_1 : List Nat := List.map Nat.succ ([1] ++ [2]) -- should equal [2, 3]
def map_append_example_2 : List Nat := List.map (· * 2) ([1, 2] ++ [3, 4]) -- should equal [2, 4, 6, 8]

-- These concrete examples should trigger the induction heuristic to discover:
-- 1. length(l1 ++ l2) = length(l1) + length(l2) for all lists l1, l2
-- 2. reverse(reverse(l)) = l for all lists l  
-- 3. map f (l1 ++ l2) = map f l1 ++ map f l2 for all f, l1, l2

-- Create initial concept list for Lists domain
def listsInitialConcepts : MetaM (List ConceptData) := do
  let mut concepts : List ConceptData := []
  
  -- Basic list constructors
  concepts := concepts ++ [
    ConceptData.definition "empty_list" (Expr.const ``List.nil [levelZero]) (Expr.const ``List.nil [levelZero]) none [] {
      name := "empty_list"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Concrete lists
  let list_exprs := [
    ("list_0", mkApp (mkConst ``List.cons [levelZero]) (mkConst ``Nat.zero)),
    ("list_1", mkApp (mkConst ``List.cons [levelZero]) (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))),
    ("list_01", mkConst ``list_01),
    ("list_10", mkConst ``list_10),
    ("list_012", mkConst ``list_012)
  ]
  
  for (name, expr) in list_exprs do
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    concepts := concepts ++ [
      ConceptData.definition name listType expr none [] {
        name := name
        created := 0
        parent := none
        interestingness := 0.9
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "seed"
      }
    ]
  
  -- Core list operations
  let operations := [
    ("List.length", "Calculate the length of a list"),
    ("List.append", "Concatenate two lists"),
    ("List.reverse", "Reverse a list"),
    ("List.map", "Apply a function to every element"),
    ("List.foldl", "Fold a list from the left"),
    ("List.filter", "Filter elements satisfying a predicate"),
    ("List.head?", "Get the first element if it exists"),
    ("List.tail", "Get all elements except the first")
  ]
  
  for (op_name, description) in operations do
    concepts := concepts ++ [
      ConceptData.heuristicRef op_name description {
        name := op_name
        created := 0
        parent := none
        interestingness := 0.95
        useCount := 0
        successCount := 0
        specializationDepth := 0
        generationMethod := "seed"
      }
    ]
  
  -- Seed specific conjectures that will trigger induction heuristic
  -- These patterns match what the induction heuristic looks for
  
  -- Length-append pattern conjectures (trigger induction)
  concepts := concepts ++ [
    ConceptData.conjecture "length_append_example_1" (mkConst ``True) 0.8 {
      name := "length_append_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "length_append_example_2" (mkConst ``True) 0.8 {
      name := "length_append_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "length_append_example_3" (mkConst ``True) 0.8 {
      name := "length_append_example_3"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Reverse-reverse pattern conjectures (trigger induction)
  concepts := concepts ++ [
    ConceptData.conjecture "reverse_reverse_example_1" (mkConst ``True) 0.8 {
      name := "reverse_reverse_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "reverse_reverse_example_2" (mkConst ``True) 0.8 {
      name := "reverse_reverse_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "reverse_reverse_example_3" (mkConst ``True) 0.8 {
      name := "reverse_reverse_example_3"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Map-append pattern conjectures (trigger induction)
  concepts := concepts ++ [
    ConceptData.conjecture "map_append_example_1" (mkConst ``True) 0.8 {
      name := "map_append_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "map_append_example_2" (mkConst ``True) 0.8 {
      name := "map_append_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  return concepts

-- Discovery configuration optimized for lists
def listsDiscoveryConfig : DiscoveryConfig := {
  maxSpecializationDepth := 4
  maxConceptsPerIteration := 100
  pruneThreshold := 0.2
  deduplicateConcepts := true
  canonicalizeConcepts := true
  filterInternalProofs := true
  enableConjectures := true
  enablePatternRecognition := true
  enableDebugOutput := true
}

def runListsDiscovery (discoveryConfig : DiscoveryConfig) (maxIterations : Nat) : MetaM Unit := do
  IO.println "=== Lists Domain Discovery - Inductive Reasoning Showcase ==="
  IO.println "This domain features lists, which are perfect for inductive discovery:"
  IO.println "- Lists are defined inductively ([] and h::t)"
  IO.println "- All operations are recursive"
  IO.println "- Theorems require induction to prove"
  IO.println ""
  
  let initialConcepts ← listsInitialConcepts
  IO.println s!"Starting with {initialConcepts.length} list concepts..."
  IO.println ""
  
  IO.println "Key patterns the induction heuristic should discover:"
  IO.println "1. length(l1 ++ l2) = length(l1) + length(l2)"
  IO.println "2. reverse(reverse(l)) = l"
  IO.println "3. map f (l1 ++ l2) = map f l1 ++ map f l2"
  IO.println "4. length(reverse(l)) = length(l)"
  IO.println "5. map f (map g l) = map (f ∘ g) l"
  IO.println ""
  
  -- Run the discovery with our seeded concepts
  let _ ← runDiscoveryCustomWithSaving "lists_discovery" initialConcepts [] [] maxIterations false discoveryConfig "log/lists_discovery"

end LeanDisco.Domains.Lists