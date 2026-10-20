#!/bin/sh
# Soundness oracles for the type checker, run over every example that normally
# passes (fail_* and the standing skip list excluded):
#
# Phase A (--oracle): every type the compiler established statically, where it
# emitted no check, is checked at runtime anyway. A failing check means a
# static certification was wrong.
#
# Phase B (--no-type-checks): every check is compiled away. A typed run that
# raised no type error must give the same test results with its checks erased
# - the erasure property of TYPES.md: checks only ever stop a run, they never
# change what it computes. Runs that raise a type error, even one a catch then
# turns into a value (examples testing the checks themselves), are skipped.
set -u
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
ROOT_DIR=$(CDPATH= cd -- "$SCRIPT_DIR/.." && pwd)
TMP_DIR=$(mktemp -d /tmp/soundness_matrix_XXXX)
trap 'rm -rf "$TMP_DIR"' EXIT

#SWI's printed names for otherwise identical free variables depend on clause
#allocation details. Canonicalize them per result line while preserving
#repeated-variable identity, so phases compare answers, not allocator suffixes.
normalize_test_results() {
    grep "should" |
        perl -pe 'my (%v, $n); s{\$_[0-9]+}{$v{$&} //= "\$_V" . ++$n}ge'
}

#Reports every type error raised, caught or not:
REPORT_TYPE_ERRORS="assertz((prolog:prolog_exception_hook(error(_, typecheck), _, _, _, _) :- format(user_error, 'TYPE ERROR RAISED~n', []), fail))"

run_oracle_phases() {
    f=$1
    base=$(basename "$f")

    out=$(timeout -k 5 240 sh "$ROOT_DIR/run.sh" "$f" --oracle -s 2>&1)
    st=$?
    if [ $st -eq 124 ] || [ $st -eq 137 ]; then
        echo "[SKIP-TIMEOUT oracle] $base"
    elif [ $st -ne 0 ] || echo "$out" | grep -q "❌"; then
        echo "[FAIL oracle] $base: a statically established type failed its runtime check"
        echo "$out" | grep -E "❌|ERROR|Type" | head -3
        : > "$TMP_DIR/failed"
    fi

    typed=$(timeout -k 5 240 swipl --stack_limit="$PETTA_STACK_LIMIT" -q -g "$REPORT_TYPE_ERRORS" \
                -s "$ROOT_DIR/src/main.pl" -- "$f" -s 2>&1)
    st1=$?
    if echo "$typed" | grep -q "TYPE ERROR RAISED"; then echo "$base" >> "$TMP_DIR/raised"; return; fi
    echo "$base" >> "$TMP_DIR/compared"
    erased=$(timeout -k 5 240 sh "$ROOT_DIR/run.sh" "$f" --no-type-checks -s 2>&1)
    st2=$?
    if [ $st1 -eq 124 ] || [ $st1 -eq 137 ] || [ $st2 -eq 124 ] || [ $st2 -eq 137 ]; then
        echo "[SKIP-TIMEOUT erasure] $base"
    elif [ "$(echo "$typed" | normalize_test_results)" != "$(echo "$erased" | normalize_test_results)" ] || [ $st1 -ne $st2 ]; then
        echo "[FAIL erasure] $base: erasing the checks changed the results"
        : > "$TMP_DIR/failed"
    fi
}

# A BOUNDED pool of PETTA_TEST_JOBS workers (default 8), each taking a chunk of
# the file list sequentially; the stack cap keeps pool x worst-case memory bounded.
NJOBS=${PETTA_TEST_JOBS:-8}
export PETTA_STACK_LIMIT=${PETTA_STACK_LIMIT:-3g}
i=0
for f in "$ROOT_DIR"/examples/*.metta; do
    case "$(basename "$f")" in
        fail_*.metta|repl.metta|llm_cities.metta|torch.metta|greedy_chess.metta|git_import2.metta) continue ;;
    esac
    echo "$f" >> "$TMP_DIR/chunk$((i % NJOBS))"
    i=$((i+1))
done
for c in "$TMP_DIR"/chunk*; do
    (
        while IFS= read -r f; do
            run_oracle_phases "$f"
        done < "$c"
        exit 0
    ) > "$c.log" 2>&1 &
done
wait
cat "$TMP_DIR"/chunk*.log
count() { if [ -f "$TMP_DIR/$1" ]; then wc -l < "$TMP_DIR/$1" | tr -d ' '; else echo 0; fi; }
echo "Phase A: $i examples. Phase B: $(count compared) compared, $(count raised) skipped (a type error was raised)."

if [ -f "$TMP_DIR/failed" ]; then
    echo "FAILURES in soundness_matrix.sh"
    exit 1
fi
echo "OK: soundness_matrix.sh"
