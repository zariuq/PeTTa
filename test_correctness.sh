#!/bin/bash
# Comprehensive correctness test suite for resolution prover
# Tests all problems < 10 clauses and verifies against MiniSat

cd /home/zar/claude/hyperon/PeTTa

TIMEOUT=30
MEMLIMIT=6291456
TESTDIR="demos/test_problems"

PASSED=0
FAILED=0
ERRORS=0

echo "======================================================================="
echo "Resolution Prover - Comprehensive Correctness Test Suite"
echo "======================================================================="
echo ""
echo "Testing all problems with < 10 clauses"
echo "Verifying results against MiniSat"
echo ""

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

test_problem() {
    local name=$1
    local file=$2
    local expected=$3

    echo "-------------------------------------------------------------------"
    echo "Test: $name"
    echo "File: $file"
    echo "Expected: $expected"

    # Get MiniSat result
    local minisat_result=$(timeout 5 minisat $file /tmp/minisat_out.txt 2>&1 | grep -E "UNSAT|SATISFIABLE" | head -1)
    echo "MiniSat: $minisat_result"

    # Get our prover result
    local our_result=$(ulimit -v $MEMLIMIT && timeout $TIMEOUT ./run.sh demos/resprover.metta $file --silent 2>&1 | grep -E '"UNSAT"|"SAT"|"UNKNOWN"' | head -1 | tr -d '"')
    echo "Our prover: $our_result"

    # Verify correctness
    local verdict="UNKNOWN"
    if [[ "$expected" == "UNSAT" ]]; then
        if [[ "$our_result" == "UNSAT" ]] && [[ "$minisat_result" == *"UNSAT"* ]]; then
            verdict="PASS"
            ((PASSED++))
        elif [[ "$our_result" == "UNSAT" ]] && [[ "$minisat_result" != *"UNSAT"* ]]; then
            verdict="FAIL - Incorrect UNSAT"
            ((FAILED++))
        elif [[ "$our_result" != "UNSAT" ]]; then
            verdict="FAIL - Expected UNSAT, got $our_result"
            ((FAILED++))
        fi
    elif [[ "$expected" == "SAT" ]]; then
        if [[ "$our_result" == "SAT" ]] && [[ "$minisat_result" == *"SATISFIABLE"* ]]; then
            verdict="PASS"
            ((PASSED++))
        elif [[ "$our_result" == "SAT" ]] && [[ "$minisat_result" != *"SATISFIABLE"* ]]; then
            verdict="FAIL - Incorrect SAT"
            ((FAILED++))
        elif [[ "$our_result" != "SAT" ]]; then
            verdict="FAIL - Expected SAT, got $our_result"
            ((FAILED++))
        fi
    else
        verdict="ERROR - Unknown expected result"
        ((ERRORS++))
    fi

    # Print verdict with color
    if [[ "$verdict" == "PASS" ]]; then
        echo -e "${GREEN}✓ $verdict${NC}"
    elif [[ "$verdict" == "ERROR"* ]]; then
        echo -e "${YELLOW}⚠ $verdict${NC}"
    else
        echo -e "${RED}✗ $verdict${NC}"
    fi

    echo ""
}

echo "### UNSAT Problems ###"
echo ""
test_problem "Minimal 3-clause contradiction" "$TESTDIR/simple_unsat_3.cnf" "UNSAT"
test_problem "Transitivity chain (6 clauses)" "$TESTDIR/transitivity_6.cnf" "UNSAT"
test_problem "XOR contradiction (4 clauses)" "$TESTDIR/xor_unsat_4.cnf" "UNSAT"
test_problem "Tautology removal (5 clauses)" "$TESTDIR/tautology_5.cnf" "UNSAT"
test_problem "PHP(3,2) - 9 clauses" "$TESTDIR/php32.cnf" "UNSAT"

echo ""
echo "### SAT Problems ###"
echo ""
test_problem "Trivial SAT (2 clauses)" "$TESTDIR/simple_sat_2.cnf" "SAT"
test_problem "Simple disjunction (3 clauses)" "$TESTDIR/disjunction_3.cnf" "SAT"
test_problem "All unit clauses (3 clauses)" "$TESTDIR/unit_clauses_3.cnf" "SAT"
test_problem "PHP(2,2) - 4 clauses" "$TESTDIR/php22.cnf" "SAT"

echo "======================================================================="
echo "Test Summary"
echo "======================================================================="
echo -e "${GREEN}Passed: $PASSED${NC}"
echo -e "${RED}Failed: $FAILED${NC}"
echo -e "${YELLOW}Errors: $ERRORS${NC}"
echo ""

TOTAL=$((PASSED + FAILED + ERRORS))
if [[ $FAILED -eq 0 ]] && [[ $ERRORS -eq 0 ]]; then
    echo -e "${GREEN}ALL TESTS PASSED! ✓${NC}"
    exit 0
else
    echo -e "${RED}SOME TESTS FAILED! ✗${NC}"
    exit 1
fi
