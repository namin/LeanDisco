# LeanDisco Testing Infrastructure

This document describes the testing framework for LeanDisco and how to ensure system reliability.

## Test Suites

### 1. Quick Test Suite (`./run_quick_tests.sh`)
**Purpose**: Rapid development feedback (< 2 minutes)  
**Use case**: Run after any code changes to catch major regressions

**Core tests**:
- ✅ `TestBasic.lean` - Core discovery engine
- ❌ `TestProofGeneration.lean` - Basic proof strategies (currently failing)
- ✅ `SimpleCurriculum.lean` - Simple curriculum system
- ✅ `TestDistributiveComplex.lean` - Extensible proof strategies
- ✅ `TestDistributive.lean` - Distributive property proofs
- ✅ `TestBenchmarksCompileOnly.lean` - Benchmark compilation
- ❌ `TestSingleGoal.lean` - Single goal testing (currently failing)

**Status**: 5/7 tests passing (71%)

### 2. Full Regression Suite (`./run_regression_tests.sh`)
**Purpose**: Comprehensive system validation  
**Use case**: Run before commits, releases, or major changes

**Test categories**:
- **Core System**: Discovery engine, heuristics, proof generation
- **Curriculum System**: Simple and complex curriculum validation
- **Proof Strategies**: Distributive property, extensible strategies
- **Domain-Specific**: Number theory, finite fields, group rings
- **Benchmark System**: MiniF2F integration, goal validation
- **Integration**: Script execution, end-to-end workflows

## Current Test Files and Their Purpose

### Core System Tests
| File | Purpose | Status |
|------|---------|--------|
| `TestBasic.lean` | Core discovery engine functionality | ✅ Working |
| `TestApplicationHeuristic.lean` | Mathematical concept application | ✅ Working |
| `TestProofGeneration.lean` | Basic proof strategies | ❌ Needs fixing |
| `TestQuantifiers.lean` | ∀ and ∃ quantifier handling | ✅ Working |

### Curriculum Tests
| File | Purpose | Status |
|------|---------|--------|
| `SimpleCurriculum.lean` | Basic statements (True, 1=1, arithmetic) | ✅ 100% pass rate |
| `ProofCurriculum.lean` | Systematic curriculum progression | ✅ Working |

### Proof Strategy Tests
| File | Purpose | Status |
|------|---------|--------|
| `TestDistributive.lean` | Distributive property a*(b+c)=a*b+a*c | ✅ Working |
| `TestDistributiveComplex.lean` | Extensible strategies for Complex numbers | ✅ Working |

### Domain-Specific Tests
| File | Purpose | Status |
|------|---------|--------|
| `TestNumberTheory.lean` | Number theory concepts | ✅ Working |
| `TestFiniteFields.lean` | Finite field mathematics | ✅ Working |
| `TestGroupRing.lean` | Group and ring theory | ✅ Working |
| `TestLists.lean` | List-based mathematical concepts | ✅ Working |
| `TestInfiniteNumbers.lean` | Infinite number systems | ✅ Working |

### Benchmark Tests
| File | Purpose | Status |
|------|---------|--------|
| `TestBenchmarks.lean` | Full MiniF2F benchmark runner | ✅ Working |
| `TestBenchmarksCompileOnly.lean` | Compilation verification | ✅ Working |
| `TestSingleGoal.lean` | Individual problem testing | ❌ Needs fixing |
| `TestBenchmarksWorking.lean` | Working subset validation | ✅ Working |

### Specialized Tests
| File | Purpose | Status |
|------|---------|--------|
| `TestTrivialProofs.lean` | Trivial statement handling | ✅ Working |
| `TestConjectureProving.lean` | Conjecture generation/proving | ✅ Working |
| `TestGoalDirected.lean` | Goal-directed discovery | ✅ Working |
| `TestComputable.lean` | Computational mathematics | ✅ Working |
| `TestAllGoals.lean` | Multi-goal processing | ✅ Working |

## Known Issues and Fixes Needed

### 1. TestProofGeneration.lean (FAILING)
**Issue**: Unknown compilation/runtime error  
**Impact**: Core proof functionality validation  
**Priority**: High

### 2. TestSingleGoal.lean (FAILING)  
**Issue**: Likely related to mathd_algebra_182 Complex number handling  
**Impact**: Individual benchmark problem testing  
**Priority**: Medium

## Usage Instructions

### For Development (Quick Feedback)
```bash
# Run after any code changes
./run_quick_tests.sh
```

### For Release/Commit (Comprehensive)
```bash
# Run full regression suite
./run_regression_tests.sh
```

### For Individual Test Debugging
```bash
# Run specific test with output
lake lean TestProofGeneration.lean

# Run with timing
time lake lean TestBasic.lean
```

## Test Environment Setup

The test scripts automatically configure:
- Stack size: `ulimit -s 65536`
- Lean stack size: `LEAN_STACK_SIZE=67108864`
- Timeout: 30s (quick), 120s (full regression)

## Adding New Tests

1. **Create test file**: Follow naming convention `Test*.lean`
2. **Add to quick suite**: If test is essential and fast (< 30s)
3. **Add to full suite**: All tests should be in regression suite
4. **Document purpose**: Update this file with test description

## Test Output Interpretation

- ✅ **PASSED**: Test completed successfully
- ❌ **FAILED**: Test failed (compilation error or assertion failure)
- ⚠️ **TIMEOUT**: Test exceeded time limit (likely infinite loop)

## Integration with Development Workflow

1. **Before making changes**: Run quick tests to establish baseline
2. **After making changes**: Run quick tests to catch immediate issues
3. **Before committing**: Run full regression suite
4. **Regular maintenance**: Monitor test status and fix failing tests

## Future Improvements

1. **Continuous Integration**: Automate test running on commits
2. **Performance Benchmarks**: Track test execution time trends
3. **Coverage Analysis**: Ensure all major code paths are tested
4. **Automated Test Generation**: Generate tests from successful discoveries