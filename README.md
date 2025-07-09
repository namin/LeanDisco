# LeanDisco

[![CI Status](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/namin/LeanDisco/actions/workflows/lean_action_ci.yml)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/namin/LeanDisco)

_Eurisko-Inspired Discovery System for Lean in Lean_

See sample outputs in [log](log) directory.

## Running

`lake build` builds the system. Then run tests:

### Core Discovery Tests
- `lake lean TestInfiniteNumbers.lean` - Infinite number discovery
- `lake lean TestFiniteFields.lean` - Finite field exploration  
- `lake lean TestNumberTheory.lean` - Number theory concepts
- `lake lean TestGroupRing.lean` - Group ring properties

### Benchmark Tests
- `lake lean TestBenchmarks.lean` - miniF2F integration test
- `lake lean BenchmarkEval.lean` - Quick benchmark evaluation

Test files also run interactively in VSCode Lean extension.

## References

- [Software Archaeology of Eurisko](https://github.com/namin/eurisclo/tree/llm): a reflective port in Common Lisp, based on unearthed original file.
- [llmlean](https://github.com/cmu-l3/llmlean/): probably a good starting point to think about LLM integration from within Lean.
