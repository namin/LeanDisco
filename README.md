# LeanDisco

[![CI Status](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/namin/LeanDisco)

_Eurisko-Inspired Discovery System for Lean in Lean_

## Running

`lake build` builds the system.
Then run tests with `lake lean _TestXXX.lean_`.
Test files also run interactively in VSCode Lean extension.

### Domain-Specific Discovery Tests
- `lake lean TestInfiniteNumbers.lean`
- `lake lean TestFiniteFields.lean`
- `lake lean TestLists.lean`
- `lake lean TestNumberTheory.lean`
- `lake lean TestGroupRing.lean`

Some of these are slow and output incrementally in [log](log) directory.

### Benchmark Tests
- `lake lean TestBenchmarks.lean` -- Full miniF2F benchmark infrastructure (0% success on hard problems)
- `lake lean TestTrivialProofs.lean` -- End-to-end proof that pipeline works (100% success on easy problems)
- `lake lean TestSingleGoal.lean` -- Diagnostic tool for testing individual theorems (configurable in file)

## References

- [Software Archaeology of Eurisko](https://github.com/namin/eurisclo/tree/llm): a reflective port in Common Lisp, based on unearthed original file.
- [llmlean](https://github.com/cmu-l3/llmlean/): probably a good starting point to think about LLM integration from within Lean.
