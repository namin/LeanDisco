#!/bin/bash

# LeanDisco Regression Test Suite
# Runs all critical tests to ensure system functionality after changes

set -e  # Exit on any error

echo "🧪 LeanDisco Regression Test Suite"
echo "=================================="
echo

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Test counters
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Function to run a test and track results
run_test() {
    local test_name="$1"
    local test_file="$2"
    local description="$3"
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    echo -e "${BLUE}[TEST $TOTAL_TESTS]${NC} $test_name"
    echo "  Description: $description"
    echo "  File: $test_file"
    
    if timeout 120 lake lean "$test_file" > /dev/null 2>&1; then
        echo -e "  ${GREEN}✅ PASSED${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo
        return 0
    else
        echo -e "  ${RED}❌ FAILED${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        echo "  Running with verbose output to show error:"
        lake lean "$test_file" || true
        echo
        return 1
    fi
}

# Function to run a test with expected output
run_test_with_output() {
    local test_name="$1"
    local test_file="$2"
    local description="$3"
    local expected_pattern="$4"
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    echo -e "${BLUE}[TEST $TOTAL_TESTS]${NC} $test_name"
    echo "  Description: $description"
    echo "  File: $test_file"
    echo "  Expected output pattern: $expected_pattern"
    
    if output=$(timeout 120 lake lean "$test_file" 2>&1) && echo "$output" | grep -q "$expected_pattern"; then
        echo -e "  ${GREEN}✅ PASSED${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
        echo
        return 0
    else
        echo -e "  ${RED}❌ FAILED${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        echo "  Actual output:"
        echo "$output" | head -20
        echo
        return 1
    fi
}

echo "🔧 Setting up test environment..."
# Increase stack size for tests
ulimit -s 65536 2>/dev/null || echo "Warning: Could not increase stack size"
export LEAN_STACK_SIZE=67108864

echo

# CORE SYSTEM TESTS
echo -e "${YELLOW}=== CORE SYSTEM TESTS ===${NC}"

run_test "Basic Discovery Engine" "TestBasic.lean" \
    "Tests core discovery system, concept generation, and heuristics"

run_test "Application Heuristic" "TestApplicationHeuristic.lean" \
    "Tests mathematical concept application and generation"

run_test "Proof Generation" "TestProofGeneration.lean" \
    "Tests basic proof strategies and theorem proving capabilities"

run_test "Quantifier Handling" "TestQuantifiers.lean" \
    "Tests ∀ and ∃ quantifier proof strategies"

# CURRICULUM TESTS  
echo -e "${YELLOW}=== CURRICULUM SYSTEM TESTS ===${NC}"

run_test_with_output "Simple Curriculum" "SimpleCurriculum.lean" \
    "Tests basic curriculum statements (True, 1=1, arithmetic)" \
    "✅ PASSED"

run_test_with_output "Proof Curriculum" "ProofCurriculum.lean" \
    "Tests systematic proof curriculum from trivial to complex" \
    "Level.*completed"

# PROOF STRATEGY TESTS
echo -e "${YELLOW}=== PROOF STRATEGY TESTS ===${NC}"

run_test_with_output "Distributive Property" "TestDistributive.lean" \
    "Tests distributive property a * (b + c) = a * b + a * c" \
    "SUCCESS.*distributive"

run_test_with_output "Extensible Proof Strategies" "TestDistributiveComplex.lean" \
    "Tests extensible proof system with Complex numbers" \
    "SUCCESS.*Nat distributive"

# DOMAIN-SPECIFIC TESTS
echo -e "${YELLOW}=== DOMAIN-SPECIFIC TESTS ===${NC}"

run_test "Number Theory" "TestNumberTheory.lean" \
    "Tests number theory concepts and proofs"

run_test "Finite Fields" "TestFiniteFields.lean" \
    "Tests finite field mathematics"

run_test "Group Ring Theory" "TestGroupRing.lean" \
    "Tests group and ring theory concepts"

# BENCHMARK SYSTEM TESTS
echo -e "${YELLOW}=== BENCHMARK SYSTEM TESTS ===${NC}"

run_test "Benchmark Compilation" "TestBenchmarksCompileOnly.lean" \
    "Tests that benchmark system compiles without errors"

run_test_with_output "Single Goal Testing" "TestSingleGoal.lean" \
    "Tests individual MiniF2F problem solving" \
    "Testing Single Goal"

# COMPILATION TESTS (quick smoke tests)
echo -e "${YELLOW}=== COMPILATION SMOKE TESTS ===${NC}"

run_test "Conjecture Proving" "TestConjectureProving.lean" \
    "Tests conjecture generation and proving system"

run_test "Goal-Directed Discovery" "TestGoalDirected.lean" \
    "Tests goal-directed mathematical discovery"

run_test "Trivial Proofs" "TestTrivialProofs.lean" \
    "Tests handling of trivial mathematical statements"

# INTEGRATION TESTS
echo -e "${YELLOW}=== INTEGRATION TESTS ===${NC}"

echo -e "${BLUE}[INTEGRATION]${NC} Benchmark Script Execution"
echo "  Description: Tests run_benchmarks.sh script functionality"
if timeout 60 ./run_benchmarks.sh > /dev/null 2>&1; then
    echo -e "  ${GREEN}✅ PASSED${NC}"
    PASSED_TESTS=$((PASSED_TESTS + 1))
else
    echo -e "  ${RED}❌ FAILED${NC}"
    FAILED_TESTS=$((FAILED_TESTS + 1))
fi
TOTAL_TESTS=$((TOTAL_TESTS + 1))
echo

# FINAL SUMMARY
echo -e "${YELLOW}=== TEST SUMMARY ===${NC}"
echo "Total tests run: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED_TESTS${NC}"
echo -e "Failed: ${RED}$FAILED_TESTS${NC}"

if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "\n${GREEN}🎉 ALL TESTS PASSED! System is working correctly.${NC}"
    exit 0
else
    echo -e "\n${RED}⚠️  $FAILED_TESTS test(s) failed. Please review the failures above.${NC}"
    exit 1
fi