#!/bin/sh

swipl -q -s tests/test_parser_swrite.pl -g run_tests -t halt || exit 1
swipl -q -s tests/test_det_folds.pl -g "run_tests(det_folds)" -t halt || exit 1
swipl -q -s tests/test_syntax_heads.pl -g "run_tests(syntax_heads)" -t halt || exit 1

run_test() {
    f="$1"
    echo "Running $f"
    output=$(sh run.sh "$f")
    error=$?
    output=$(echo "$output"  | grep "is " | grep " should ")
    echo "$output" | grep -q "❌"
    fail=$?
    echo "$output" | grep -q "✅"
    pass=$?
    if [ $error -ne 0 ] || [ $fail -eq 0 ] || [ $pass -ne 0 ]; then
        echo "FAILURE in $f:"
        echo "$output"
        return 1
    else
        echo "OK: $f"
        echo "$output"
        return 0
    fi
}

# fail_* examples must stop with a type error (at compile time or at runtime)
# or a syntax error:
run_expected_fail_test() {
    f="$1"
    echo "Running (expected fail) $f"
    output=$(sh run.sh "$f" 2>&1)
    status=$?
    if [ $status -eq 0 ]; then
        echo "FAILURE in $f:"
        echo "Expected non-zero exit status, got success"
        return 1
    fi
    echo "$output" | grep -E -q "Type mismatch|Type conflict|No matching typed overload|Refinement:|Syntax error|Determinism:"
    if [ $? -ne 0 ]; then
        echo "FAILURE in $f:"
        echo "Expected type error output"
        echo "$output"
        return 1
    fi
    echo "OK (failed as expected): $f"
    return 0
}

# The examples run in a BOUNDED pool: PETTA_TEST_JOBS chunks (default 8), each
# a background worker running its share sequentially. Unbounded fan-out - one
# swipl per example, ~290 at once - could exhaust RAM and take the machine
# down; the pool keeps peak memory at jobs x stack cap by construction, which
# is also why the harness lowers run.sh's stack limit here (override either
# knob in the environment). Failures are collected and reported at the end
# instead of killing the run: verdicts are unchanged, only scheduling is.
run_one_example() {
    case "$(basename "$1")" in
        fail_*.metta) run_expected_fail_test "$1" ;;
        *)            run_test "$1" ;;
    esac
}

NJOBS=${PETTA_TEST_JOBS:-8}
# 3g: the smallest cap the heaviest example (matespacefast) fits in, and
# 8 x 3g bounds the pool's worst case below the machine:
export PETTA_STACK_LIMIT=${PETTA_STACK_LIMIT:-3g}
TMPD=$(mktemp -d /tmp/petta_test_XXXX)
i=0
for f in ./examples/*.metta; do
    base=$(basename "$f")
    case "$base" in repl.metta|llm_cities.metta|torch.metta|greedy_chess.metta|git_import2.metta)
        continue ;;
    esac
    echo "$f" >> "$TMPD/chunk$((i % NJOBS))"
    i=$((i+1))
done

for c in "$TMPD"/chunk*; do
    (
        while IFS= read -r f; do
            if ! run_one_example "$f"; then
                echo "$f" >> "$TMPD/failed"
            fi
        done < "$c"
        exit 0
    ) > "$c.log" 2>&1 &
done
wait

cat "$TMPD"/chunk*.log
status=0
if [ -f "$TMPD/failed" ]; then
    echo ""
    echo "==============================="
    echo "Failed tests:"
    sed 's/^/❌ /' "$TMPD/failed"
    echo "==============================="
    status=1
fi
rm -rf "$TMPD"

if [ $status -eq 0 ]; then
    echo ""
    echo "Running examples/type_dispatch_matrix.sh"
    if sh examples/type_dispatch_matrix.sh; then
        echo "OK: type_dispatch_matrix.sh"
    else
        echo "FAILURE in type_dispatch_matrix.sh"
        status=1
    fi
    # Typing and determinism tests, compared on full output (tests/*/run.sh):
    for suite in typing det; do
        echo ""
        echo "Running tests/$suite/run.sh"
        if sh tests/$suite/run.sh; then
            echo "OK: tests/$suite"
        else
            echo "FAILURE in tests/$suite"
            status=1
        fi
    done
    # Generated typed programs: checked, oracle and erased runs agree (a wider
    # sweep: python3 tests/typing/differential.py --n 500 --seed <other>):
    if command -v python3 > /dev/null; then
        echo ""
        echo "Running tests/typing/differential.py"
        if python3 tests/typing/differential.py --n 80 --seed 1; then
            echo "OK: differential typing audit"
        else
            echo "FAILURE in differential typing audit"
            status=1
        fi
    fi
fi

# Soundness oracles (2-3 extra runs per example; skip with SKIP_SOUNDNESS=1):
if [ $status -eq 0 ] && [ "${SKIP_SOUNDNESS:-0}" != "1" ]; then
    echo ""
    echo "Running examples/soundness_matrix.sh"
    if sh examples/soundness_matrix.sh; then
        echo "OK: soundness_matrix.sh"
    else
        echo "FAILURE in soundness_matrix.sh"
        status=1
    fi
fi

exit $status
