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
- `lake lean TestBenchmarks.lean` - Full miniF2F benchmark infrastructure (0% success on hard problems)
- `lake lean TestTrivialProofs.lean` - **End-to-end proof** that pipeline works (100% success on easy problems)
- `lake lean TestSingleGoal.lean` - Diagnostic tool for testing individual theorems

#### miniF2F Integration Status

**✅ Working**: The discovery system successfully integrates with miniF2F and can prove theorems.

**Proof of Success**: `TestTrivialProofs.lean` demonstrates 100% success rate on easy theorems like `mathd_numbertheory_169` (proven by `Eq.refl`).

**Current Limitation**: Complex theorems requiring advanced tactics like `ring`, `simp`, or `sorry` are not yet supported.

#### Test File Guide

| File | Purpose | Expected Result |
|------|---------|-----------------|
| `TestBenchmarks.lean` | Full benchmark infrastructure with 5 mixed-difficulty problems | 0% success (hard problems dominate) |
| `TestTrivialProofs.lean` | **Proof of concept** - easy theorems only | 100% success - **shows pipeline works** |
| `TestSingleGoal.lean` | Test individual theorems with configurable difficulty | Varies by theorem difficulty |

#### Using TestSingleGoal.lean

Test individual theorems from the miniF2F benchmark:

```lean
-- Edit the #eval line in TestSingleGoal.lean:
#eval testSingleGoal "mathd_numbertheory_169"  -- Easy (should work)
#eval testSingleGoal "mathd_algebra_182"       -- Hard (will fail)
```

Or run with the default easy theorem:
```bash
lake lean TestSingleGoal.lean
```

Test files also run interactively in VSCode Lean extension.

## References

- [Software Archaeology of Eurisko](https://github.com/namin/eurisclo/tree/llm): a reflective port in Common Lisp, based on unearthed original file.
- [llmlean](https://github.com/cmu-l3/llmlean/): probably a good starting point to think about LLM integration from within Lean.
