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
def length_append_example_4 : Nat := List.length ([1, 2, 3] ++ [4, 5]) -- should equal 5
def length_append_example_5 : Nat := List.length (list_012 ++ list_210) -- should equal 6

def reverse_reverse_example_1 : List Nat := List.reverse (List.reverse [1]) -- should equal [1]
def reverse_reverse_example_2 : List Nat := List.reverse (List.reverse [1, 2]) -- should equal [1, 2]
def reverse_reverse_example_3 : List Nat := List.reverse (List.reverse [1, 2, 3]) -- should equal [1, 2, 3]
def reverse_reverse_example_4 : List Nat := List.reverse (List.reverse []) -- should equal []
def reverse_reverse_example_5 : List Nat := List.reverse (List.reverse list_012) -- should equal [0, 1, 2]

def map_append_example_1 : List Nat := List.map Nat.succ ([1] ++ [2]) -- should equal [2, 3]
def map_append_example_2 : List Nat := List.map (· * 2) ([1, 2] ++ [3, 4]) -- should equal [2, 4, 6, 8]
def map_append_example_3 : List Nat := List.map (· + 1) ([] ++ [1, 2]) -- should equal [2, 3]
def map_append_example_4 : List Nat := List.map Nat.succ (list_01 ++ list_10) -- should equal [1, 2, 2, 1]

-- More challenging patterns for advanced induction detection

-- Nested structural operations
def length_reverse_example_1 : Nat := List.length (List.reverse [1, 2, 3]) -- should equal 3
def length_reverse_example_2 : Nat := List.length (List.reverse ([] : List Nat)) -- should equal 0
def length_reverse_example_3 : Nat := List.length (List.reverse list_012) -- should equal 3

-- Commutative operations
def append_assoc_example_1 : List Nat := ([1] ++ [2]) ++ [3] -- should equal [1, 2, 3]
def append_assoc_example_2 : List Nat := [1] ++ ([2] ++ [3]) -- should equal [1, 2, 3]
def append_assoc_example_3 : List Nat := ([] ++ [1]) ++ [2] -- should equal [1, 2]
def append_assoc_example_4 : List Nat := [] ++ ([1] ++ [2]) -- should equal [1, 2]

-- Filter distributivity patterns
def filter_append_example_1 : List Nat := List.filter (· > 1) ([1, 2] ++ [0, 3])
def filter_append_example_2 : List Nat := List.filter (· > 1) [1, 2] ++ List.filter (· > 1) [0, 3]
def filter_append_example_3 : List Nat := List.filter (· % 2 = 0) (list_01 ++ list_012)
def filter_append_example_4 : List Nat := List.filter (· % 2 = 0) list_01 ++ List.filter (· % 2 = 0) list_012

-- Fold distributivity patterns
def fold_append_example_1 : Nat := List.foldl (· + ·) 0 ([1, 2] ++ [3, 4])
def fold_append_example_2 : Nat := List.foldl (· + ·) (List.foldl (· + ·) 0 [1, 2]) [3, 4]
def fold_append_example_3 : Nat := List.foldl (· * ·) 1 ([2, 3] ++ [4])
def fold_append_example_4 : Nat := List.foldl (· * ·) (List.foldl (· * ·) 1 [2, 3]) [4]

-- Complex nested patterns that require sophisticated induction
def map_map_example_1 : List Nat := List.map (· + 1) (List.map (· * 2) [1, 2, 3])
def map_map_example_2 : List Nat := List.map (fun x => (x * 2) + 1) [1, 2, 3]
def map_map_example_3 : List Nat := List.map Nat.succ (List.map Nat.succ [0, 1, 2])
def map_map_example_4 : List Nat := List.map (fun x => x + 2) [0, 1, 2]

-- Identity patterns
def append_nil_left_example_1 : List Nat := [] ++ [1, 2]
def append_nil_left_example_2 : List Nat := [1, 2]
def append_nil_right_example_1 : List Nat := [1, 2] ++ []
def append_nil_right_example_2 : List Nat := [1, 2]

-- More complex recursive structures for challenging the heuristic
def nested_reverse_example_1 : List Nat := List.reverse (List.reverse (List.reverse [1, 2]))
def nested_reverse_example_2 : List Nat := List.reverse [1, 2]

-- Multi-step inductive patterns
def length_map_example_1 : Nat := List.length (List.map Nat.succ [1, 2, 3])
def length_map_example_2 : Nat := List.length [1, 2, 3]
def length_map_example_3 : Nat := List.length (List.map (· * 2) ([] : List Nat))
def length_map_example_4 : Nat := List.length ([] : List Nat)

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
    },
    ConceptData.conjecture "map_append_example_3" (mkConst ``True) 0.8 {
      name := "map_append_example_3"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "map_append_example_4" (mkConst ``True) 0.8 {
      name := "map_append_example_4"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Advanced pattern conjectures (challenging the heuristic)
  
  -- Length-reverse patterns
  concepts := concepts ++ [
    ConceptData.conjecture "length_reverse_example_1" (mkConst ``True) 0.8 {
      name := "length_reverse_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "length_reverse_example_2" (mkConst ``True) 0.8 {
      name := "length_reverse_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "length_reverse_example_3" (mkConst ``True) 0.8 {
      name := "length_reverse_example_3"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Append associativity patterns
  concepts := concepts ++ [
    ConceptData.conjecture "append_assoc_example_1" (mkConst ``True) 0.8 {
      name := "append_assoc_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "append_assoc_example_2" (mkConst ``True) 0.8 {
      name := "append_assoc_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "append_assoc_example_3" (mkConst ``True) 0.8 {
      name := "append_assoc_example_3"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Filter-append patterns
  concepts := concepts ++ [
    ConceptData.conjecture "filter_append_example_1" (mkConst ``True) 0.8 {
      name := "filter_append_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "filter_append_example_2" (mkConst ``True) 0.8 {
      name := "filter_append_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Map-map composition patterns
  concepts := concepts ++ [
    ConceptData.conjecture "map_map_example_1" (mkConst ``True) 0.8 {
      name := "map_map_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "map_map_example_2" (mkConst ``True) 0.8 {
      name := "map_map_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Length-map patterns
  concepts := concepts ++ [
    ConceptData.conjecture "length_map_example_1" (mkConst ``True) 0.8 {
      name := "length_map_example_1"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "length_map_example_2" (mkConst ``True) 0.8 {
      name := "length_map_example_2"
      created := 0
      parent := none
      interestingness := 0.85
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]

  -- Direct inductive theorem seeds (the actual inductive statements)
  
  -- Base cases for key inductive theorems
  concepts := concepts ++ [
    ConceptData.conjecture "length_append_base_case" (mkConst ``True) 0.9 {
      name := "length_append_base_case"
      created := 0
      parent := none
      interestingness := 0.95
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "reverse_reverse_base_case" (mkConst ``True) 0.9 {
      name := "reverse_reverse_base_case"
      created := 0
      parent := none
      interestingness := 0.95
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "map_append_base_case" (mkConst ``True) 0.9 {
      name := "map_append_base_case"
      created := 0
      parent := none
      interestingness := 0.95
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Inductive steps for key theorems
  concepts := concepts ++ [
    ConceptData.conjecture "length_append_inductive_step" (mkConst ``True) 0.9 {
      name := "length_append_inductive_step"
      created := 0
      parent := none
      interestingness := 0.95
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "reverse_reverse_inductive_step" (mkConst ``True) 0.9 {
      name := "reverse_reverse_inductive_step"
      created := 0
      parent := none
      interestingness := 0.95
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "map_append_inductive_step" (mkConst ``True) 0.9 {
      name := "map_append_inductive_step"
      created := 0
      parent := none
      interestingness := 0.95
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    }
  ]
  
  -- Full inductive theorems (what we want the system to discover)
  concepts := concepts ++ [
    ConceptData.conjecture "theorem_length_append_inductive" (mkConst ``True) 0.95 {
      name := "theorem_length_append_inductive"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "theorem_reverse_reverse_inductive" (mkConst ``True) 0.95 {
      name := "theorem_reverse_reverse_inductive"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "theorem_map_append_inductive" (mkConst ``True) 0.95 {
      name := "theorem_map_append_inductive"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "theorem_append_assoc_inductive" (mkConst ``True) 0.95 {
      name := "theorem_append_assoc_inductive"
      created := 0
      parent := none
      interestingness := 1.0
      useCount := 0
      successCount := 0
      specializationDepth := 0
      generationMethod := "seed"
    },
    ConceptData.conjecture "theorem_length_reverse_inductive" (mkConst ``True) 0.95 {
      name := "theorem_length_reverse_inductive"
      created := 0
      parent := none
      interestingness := 1.0
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

/-- List-specific inductive theorem statement generation -/
def createListInductiveTheoremStatement (pattern : String) : MetaM Expr := do
  -- Helper to create forall expressions
  let mkForallExpr (varName : String) (varType : Expr) (body : Expr) : Expr :=
    Expr.forallE (Name.mkSimple varName) varType body (BinderInfo.default)
  
  -- Helper to create equality expressions
  let mkEqualityExpr (left : Expr) (right : Expr) (type : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [levelOne]) type left right
  
  match pattern with
  | "length" | "length_append" => 
    -- Generate: ∀ l1 l2, length(l1 ++ l2) = length(l1) + length(l2)
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l1") listType fun l1Var => do
    withLocalDeclD (Name.mkSimple "l2") listType fun l2Var => do
      -- length(l1 ++ l2)
      let append := mkApp2 (mkConst ``List.append [levelZero]) l1Var l2Var
      let leftSide := mkApp (mkConst ``List.length [levelZero]) append
      
      -- length(l1) + length(l2)
      let len1 := mkApp (mkConst ``List.length [levelZero]) l1Var
      let len2 := mkApp (mkConst ``List.length [levelZero]) l2Var
      let rightSide := mkApp2 (mkConst ``Nat.add) len1 len2
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide (mkConst ``Nat)
      let forallL2 := mkForallExpr "l2" listType equality
      let forallL1 := mkForallExpr "l1" listType forallL2
      
      return forallL1
    
  | "append" =>
    -- Generate: ∀ l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)  
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l1") listType fun l1Var => do
    withLocalDeclD (Name.mkSimple "l2") listType fun l2Var => do
    withLocalDeclD (Name.mkSimple "l3") listType fun l3Var => do
      -- (l1 ++ l2) ++ l3
      let l1l2 := mkApp2 (mkConst ``List.append [levelZero]) l1Var l2Var
      let leftSide := mkApp2 (mkConst ``List.append [levelZero]) l1l2 l3Var
      
      -- l1 ++ (l2 ++ l3)
      let l2l3 := mkApp2 (mkConst ``List.append [levelZero]) l2Var l3Var
      let rightSide := mkApp2 (mkConst ``List.append [levelZero]) l1Var l2l3
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide listType
      let forallL3 := mkForallExpr "l3" listType equality
      let forallL2 := mkForallExpr "l2" listType forallL3
      let forallL1 := mkForallExpr "l1" listType forallL2
      
      return forallL1
    
  | "reverse" =>
    -- Generate: ∀ l, reverse(reverse(l)) = l
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l") listType fun lVar => do
      -- reverse(reverse(l))
      let rev1 := mkApp (mkConst ``List.reverse [levelZero]) lVar
      let leftSide := mkApp (mkConst ``List.reverse [levelZero]) rev1
      
      -- l
      let rightSide := lVar
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide listType
      let forallL := mkForallExpr "l" listType equality
      
      return forallL
    
  | _ =>
    -- Fallback for other patterns
    IO.println s!"[LISTS] No specific theorem template for pattern: {pattern}"
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    let body := mkConst ``True
    return mkForallExpr s!"{pattern}_var" listType body

/-- Generate List-specific composition theorems -/
def generateListCompositionTheorem (op1 op2 : String) : MetaM (Option (String × Expr)) := do
  try
    -- Only generate for meaningful List operation combinations
    if (contains op1 "length" && contains op2 "append") then
      -- length(l1 ++ l2) = length(l1) + length(l2)
      let theoremName := "length_append_distributive"
      let statement ← createListInductiveTheoremStatement "length"
      return some (theoremName, statement)
    else if (contains op1 "append" && contains op2 "append") then
      -- (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
      let theoremName := "append_associative"
      let statement ← createListInductiveTheoremStatement "append"
      return some (theoremName, statement)
    else
      return none
  catch e =>
    return none

/-- Generate List-specific self-inverse theorems -/
def generateListSelfInverseTheorem (op : String) : MetaM (Option (String × Expr)) := do
  try
    if contains op "reverse" then
      -- reverse(reverse(l)) = l
      let theoremName := "reverse_involutive"
      let statement ← createListInductiveTheoremStatement "reverse"
      return some (theoremName, statement)
    else
      return none
  catch e =>
    return none

/-- Domain-specific theorem statement creation for Lists -/
def createListTheoremStatement (pattern : String) : MetaM Expr := do
  -- Helper functions
  let mkForallExpr (varName : String) (varType : Expr) (body : Expr) : Expr :=
    Expr.forallE (Name.mkSimple varName) varType body (BinderInfo.default)
  
  let mkEqualityExpr (left : Expr) (right : Expr) (type : Expr) : Expr :=
    mkApp3 (mkConst ``Eq [levelOne]) type left right
  
  match pattern with
  | "length_append" | "length" => 
    -- Generate: ∀ l1 l2, length(l1 ++ l2) = length(l1) + length(l2)
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l1") listType fun l1Var => do
    withLocalDeclD (Name.mkSimple "l2") listType fun l2Var => do
      -- length(l1 ++ l2)
      let append := mkApp2 (mkConst ``List.append [levelZero]) l1Var l2Var
      let leftSide := mkApp (mkConst ``List.length [levelZero]) append
      
      -- length(l1) + length(l2)
      let len1 := mkApp (mkConst ``List.length [levelZero]) l1Var
      let len2 := mkApp (mkConst ``List.length [levelZero]) l2Var
      let rightSide := mkApp2 (mkConst ``Nat.add) len1 len2
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide (mkConst ``Nat)
      let forallL2 := mkForallExpr "l2" listType equality
      let forallL1 := mkForallExpr "l1" listType forallL2
      
      return forallL1
    
  | "append" =>
    -- Generate: ∀ l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)  
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l1") listType fun l1Var => do
    withLocalDeclD (Name.mkSimple "l2") listType fun l2Var => do
    withLocalDeclD (Name.mkSimple "l3") listType fun l3Var => do
      -- (l1 ++ l2) ++ l3
      let l1l2 := mkApp2 (mkConst ``List.append [levelZero]) l1Var l2Var
      let leftSide := mkApp2 (mkConst ``List.append [levelZero]) l1l2 l3Var
      
      -- l1 ++ (l2 ++ l3)
      let l2l3 := mkApp2 (mkConst ``List.append [levelZero]) l2Var l3Var
      let rightSide := mkApp2 (mkConst ``List.append [levelZero]) l1Var l2l3
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide listType
      let forallL3 := mkForallExpr "l3" listType equality
      let forallL2 := mkForallExpr "l2" listType forallL3
      let forallL1 := mkForallExpr "l1" listType forallL2
      
      return forallL1
    
  | "reverse" =>
    -- Generate: ∀ l, reverse(reverse(l)) = l
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    
    withLocalDeclD (Name.mkSimple "l") listType fun lVar => do
      -- reverse(reverse(l))
      let rev1 := mkApp (mkConst ``List.reverse [levelZero]) lVar
      let leftSide := mkApp (mkConst ``List.reverse [levelZero]) rev1
      
      -- l
      let rightSide := lVar
      
      -- Equality
      let equality := mkEqualityExpr leftSide rightSide listType
      let forallL := mkForallExpr "l" listType equality
      
      return forallL
    
  | _ =>
    -- Fallback
    IO.println s!"[LISTS] No specific theorem template for pattern: {pattern}"
    let listType := mkApp (mkConst ``List [levelZero]) (mkConst ``Nat)
    let body := mkConst ``True
    return mkForallExpr s!"{pattern}_var" listType body

end LeanDisco.Domains.Lists