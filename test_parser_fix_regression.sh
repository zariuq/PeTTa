#!/bin/bash
# Test that parser fix doesn't break existing examples
# Focus on examples at risk: strings, complex syntax, nested structures

set -e

echo "=========================================="
echo "Parser Fix Regression Test Suite"
echo "Branch: quotedparensfix"
echo "=========================================="
echo ""

TOTAL=0
PASSED=0
FAILED=0

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

run_test() {
    local example="$1"
    local description="$2"

    echo "-------------------------------------------"
    echo "Test: $description"
    echo "File: examples/$example"

    TOTAL=$((TOTAL + 1))

    # Run with 5 second timeout
    if timeout 5 ./run.sh "examples/$example" --silent > /dev/null 2>&1; then
        echo -e "${GREEN}✓ PASSED${NC}"
        PASSED=$((PASSED + 1))
    else
        local exit_code=$?
        if [ $exit_code -eq 124 ]; then
            echo -e "${RED}✗ FAILED - TIMEOUT${NC}"
        else
            echo -e "${RED}✗ FAILED - Exit code $exit_code${NC}"
        fi
        FAILED=$((FAILED + 1))

        # Show error output
        echo ""
        echo "Error output:"
        timeout 5 ./run.sh "examples/$example" --silent 2>&1 | tail -20
    fi

    echo ""
}

# High risk: Examples with strings
echo "=========================================="
echo "PART 1: Examples with Strings (HIGH RISK)"
echo "=========================================="
echo ""

run_test "he_quoting.metta" "HE quoting features"
run_test "greedy_chess.metta" "Complex chess example with strings"
run_test "gpt.metta" "GPT example (likely has strings)"
run_test "curry.metta" "Curry example"

# Medium risk: Complex syntax
echo "=========================================="
echo "PART 2: Complex Syntax (MEDIUM RISK)"
echo "=========================================="
echo ""

run_test "case.metta" "Case statements"
run_test "letstar.metta" "Let* bindings"
run_test "collapse.metta" "Collapse operations"
run_test "let_superpose_if_case.metta" "Combined constructs"

# Low risk: Basic examples (should still work)
echo "=========================================="
echo "PART 3: Basic Examples (LOW RISK)"
echo "=========================================="
echo ""

run_test "factorial.metta" "Factorial recursion"
run_test "if.metta" "Basic conditionals"

# Summary
echo "=========================================="
echo "Test Summary"
echo "=========================================="
echo ""
echo "Total tests: $TOTAL"
echo -e "Passed: ${GREEN}$PASSED${NC}"
if [ $FAILED -gt 0 ]; then
    echo -e "Failed: ${RED}$FAILED${NC}"
else
    echo "Failed: 0"
fi
echo ""

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}✓ All regression tests PASSED! ✓${NC}"
    echo "Parser fix is backward compatible."
    exit 0
else
    echo -e "${RED}✗ Some tests FAILED ✗${NC}"
    echo "Parser fix may have introduced regressions."
    exit 1
fi
