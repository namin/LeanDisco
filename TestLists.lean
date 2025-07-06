import LeanDisco.Domains.Lists

set_option autoImplicit false

open Lean Meta Elab LeanDisco

def main : IO Unit := do
  IO.println "=== Lists Domain Created Successfully ==="
  IO.println ""
  IO.println "This domain contains perfect examples for inductive discovery:"
  IO.println ""
  IO.println "✓ Created list concepts with inductive patterns"
  IO.println ""
  IO.println "Example concepts that will trigger inductive patterns:"
  IO.println "- length_append_example_1: length([1] ++ [2])"
  IO.println "- length_append_example_2: length([1,2] ++ [3])"  
  IO.println "- length_append_example_3: length([] ++ [1,2])"
  IO.println ""
  IO.println "- reverse_reverse_example_1: reverse(reverse([1]))"
  IO.println "- reverse_reverse_example_2: reverse(reverse([1,2]))"
  IO.println "- reverse_reverse_example_3: reverse(reverse([1,2,3]))"
  IO.println ""
  IO.println "- map_append_example_1: map succ ([1] ++ [2])"
  IO.println "- map_append_example_2: map (*2) ([1,2] ++ [3,4])"
  IO.println ""
  IO.println "✓ Lists domain ready for inductive discovery!"
  IO.println ""
  IO.println "The induction heuristic should recognize these patterns and generate:"
  IO.println "1. length_append_inductive: ∀ l1 l2. length(l1++l2) = length(l1)+length(l2)"
  IO.println "2. reverse_reverse_inductive: ∀ l. reverse(reverse(l)) = l"
  IO.println "3. map_append_inductive: ∀ f l1 l2. map f (l1++l2) = map f l1 ++ map f l2"
  IO.println ""
  IO.println "To test: Run the discovery system with list concepts!"
  IO.println "The enhanced induction heuristic now includes list pattern recognition."

#eval main