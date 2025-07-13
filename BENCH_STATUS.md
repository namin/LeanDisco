# Benchmark Status - MiniF2F Dataset

## Overview
This document tracks the status of the MiniF2F benchmark dataset for LeanDisco, including problematic theorems that need to be excluded to prevent stack overflow errors.

## Current Status
- **Total problems in original dataset**: 488
- **Currently excluded problems**: 1
- **Working dataset size**: 486 problems ✅
- **Success rate**: 99.6% coverage

## Excluded Problems

### mathd_algebra_433
- **Line number**: 62 (in original minif2f_lean4.jsonl)
- **Theorem**: `theorem mathd_algebra_433 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 3 * Real.sqrt (2 * x - 7) - 8) : f 8 = 19 := sorry`
- **Issue**: Causes stack overflow in Lean's expression equality test
- **Error**: `libc++abi: terminating due to uncaught exception of type lean::stack_space_exception: deep recursion was detected at 'expression equality test'`
- **Hypothesis**: The `Real.sqrt` function combined with complex arithmetic expressions triggers deep recursion in Lean's type checker
- **Impact**: Removing this single theorem allows the full dataset to work (61 → 486 problems)

## Files Modified
- **Original**: `benchmarks/miniF2F-lean4/minif2f_lean4.jsonl` (488 problems)
- **Working**: `benchmarks/miniF2F-lean4/minif2f_lean4_skip62.jsonl` (486 problems)
- **Backup**: `benchmarks/miniF2F-lean4/minif2f_lean4_backup.jsonl`

## Investigation History
1. **Initial limit**: 50 problems (original configuration)
2. **After optimization**: 61 problems (disabled deduplication/canonicalization, increased stack limits)
3. **After excluding mathd_algebra_433**: 486 problems (full dataset minus 1)

## Testing Protocol
To test for additional problematic theorems:
1. Start with current working dataset (486 problems)
2. Add back excluded theorems one by one
3. Test for stack overflow
4. Document any new problematic theorems found

## Potentially Problematic Theorems (to investigate)
The following theorems contain complex `Real.sqrt` expressions that may cause similar issues:

### imo_1965_1 (line 26)
- **Theorem**: Complex nested sqrt expressions: `abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x)))`
- **Status**: ⚠️ Needs testing
- **Risk**: High (multiple nested sqrt with trigonometric functions)

### amc12a_2019_21 (line 1) 
- **Theorem**: `z = (1 + Complex.I) / Real.sqrt 2`
- **Status**: ⚠️ Needs testing  
- **Risk**: Medium (Complex + Real.sqrt combination)

### mathd_algebra_116 (line 7)
- **Theorem**: `x = (13 - Real.sqrt 131) / 4`
- **Status**: ⚠️ Needs testing
- **Risk**: Medium (arithmetic with sqrt)

## Next Steps
- [x] Verify current status by testing full 486 problem dataset (✅ Working)
- [x] Confirm mathd_algebra_433 breaks the system (✅ Confirmed)
- [ ] Test potentially problematic theorems one by one
- [ ] Investigate if problematic theorems can be fixed instead of excluded
- [ ] Maximize dataset coverage by systematic exclusion
- [ ] Consider alternative representations for problematic theorems

## Notes
- The issue appears to be specific to certain mathematical expressions that cause deep recursion in Lean's expression equality test
- Stack size increases (up to 64MB) did not resolve the issue
- The problem occurs during compilation/type-checking, not runtime execution