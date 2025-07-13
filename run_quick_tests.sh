#!/bin/bash

# LeanDisco Quick Test Suite
# Runs essential tests for rapid development feedback (< 2 minutes)

set -e

echo "⚡ LeanDisco Quick Test Suite"
echo "============================="
echo

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

run_quick_test() {
    local test_name="$1"
    local test_file="$2"
    
    TOTAL_TESTS=$((TOTAL_TESTS + 1))
    
    echo -e "${BLUE}[QUICK TEST $TOTAL_TESTS]${NC} $test_name"
    
    if timeout 30 lake lean "$test_file" > /dev/null 2>&1; then
        echo -e "  ${GREEN}✅ PASSED${NC}"
        PASSED_TESTS=$((PASSED_TESTS + 1))
    else
        echo -e "  ${RED}❌ FAILED${NC}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
    fi
    echo
}

echo "🔧 Setting up..."
ulimit -s 65536 2>/dev/null || true
export LEAN_STACK_SIZE=67108864

# Essential functionality tests
echo -e "${YELLOW}=== CORE FUNCTIONALITY ===${NC}"
run_quick_test "Basic Discovery" "TestBasic.lean"
run_quick_test "Proof Generation" "TestProofGeneration.lean"
run_quick_test "Simple Curriculum" "SimpleCurriculum.lean"

echo -e "${YELLOW}=== RECENT CHANGES ===${NC}"
run_quick_test "Extensible Strategies" "TestDistributiveComplex.lean"
run_quick_test "Distributive Property" "TestDistributive.lean"

echo -e "${YELLOW}=== COMPILATION CHECKS ===${NC}"
run_quick_test "Benchmark System" "TestBenchmarksCompileOnly.lean"
run_quick_test "Single Goal Test" "TestSingleGoal.lean"

# Summary
echo -e "${YELLOW}=== QUICK TEST SUMMARY ===${NC}"
echo "Total: $TOTAL_TESTS | Passed: ${GREEN}$PASSED_TESTS${NC} | Failed: ${RED}$FAILED_TESTS${NC}"

if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "\n${GREEN}⚡ All quick tests passed! Ready to proceed.${NC}"
    exit 0
else
    echo -e "\n${RED}⚠️  $FAILED_TESTS quick test(s) failed. Run full regression tests for details.${NC}"
    exit 1
fi