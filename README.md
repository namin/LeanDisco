# LeanDisco

[![CI Status](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml)

_Eurisko-Inspired Discovery System for Lean in Lean_

See sample outputs in [log](log) directory.

## Running

`lake build` builds the system. Then, run a test file:
- `lake lean TestInfiniteNumbers.lean`
- `lake lean TestFiniteFields.lean`
- `lake lean TestGroupRing.lean` (slow, but shows incremental progress for each iteration in the [`log`](log) directory, for example [`log/groupring_discovery_iteration_3.txt`](log/groupring_discovery_iteration_3.txt) for iteration 3)

The test files lso run interactively in the VSCode Lean extension.

## References

- [Software Archaeology of Eurisko](https://github.com/namin/eurisclo/tree/llm): a reflective port in Common Lisp, based on unearthed original file.
- [llmlean](https://github.com/cmu-l3/llmlean/): probably a good starting point to think about LLM integration from within Lean.
