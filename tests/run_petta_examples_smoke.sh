#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/.." && pwd)
RUN_SH=${RUN_SH:-"$ROOT/run.sh"}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
LIMIT_KB=${LIMIT_KB:-10485760}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
LOG=${LOG:-"$HE_LOG_DIR/petta_examples_smoke_$(date -u +%Y%m%dT%H%M%SZ).log"}

ulimit -v "$LIMIT_KB"
mkdir -p "$(dirname -- "$LOG")"
: > "$LOG"

total=0
ran=0
skipped=0
passed=0
failed=0
timed_out=0

skip_reason() {
    case "$(basename -- "$1")" in
        he_*.metta) printf 'HE profile example; covered by run_he_profile_suite.sh under --he' ;;
        test_unify_eval_branches.metta) printf 'HE/lib_he compatibility example; covered under --he' ;;
        greedy_chess.metta) printf 'interactive chess REPL' ;;
        repl.metta) printf 'interactive REPL' ;;
        llm_cities.metta) printf 'external LLM/API example' ;;
        torch.metta) printf 'external PyTorch dependency' ;;
        git_import.metta) printf 'network git import' ;;
        git_import2.metta) printf 'network git import plus build step' ;;
        *) return 1 ;;
    esac
}

run_one() {
    local file=$1
    local rel=${file#"$ROOT"/}
    local reason out rc
    total=$((total + 1))

    if reason=$(skip_reason "$file"); then
        skipped=$((skipped + 1))
        printf 'SKIP %s (%s)\n' "$rel" "$reason" | tee -a "$LOG"
        return
    fi

    ran=$((ran + 1))
    set +e
    out=$(timeout "$TIMEOUT_SECONDS" "$RUN_SH" "$file" 2>&1)
    rc=$?
    set -e

    if [ "$rc" = 124 ]; then
        timed_out=$((timed_out + 1))
        printf 'TIMEOUT %s\n' "$rel" | tee -a "$LOG"
        printf '%s\n' "$out" | tail -40 >> "$LOG"
    elif [ "$rc" != 0 ]; then
        failed=$((failed + 1))
        printf 'FAIL %s exit=%s\n' "$rel" "$rc" | tee -a "$LOG"
        printf '%s\n' "$out" | tail -80 >> "$LOG"
    elif printf '%s\n' "$out" | grep -q '❌\|Assertion failed:'; then
        failed=$((failed + 1))
        printf 'FAIL %s output-marker\n' "$rel" | tee -a "$LOG"
        printf '%s\n' "$out" | tail -80 >> "$LOG"
    else
        passed=$((passed + 1))
        printf 'PASS %s\n' "$rel" | tee -a "$LOG"
    fi
}

while IFS= read -r file; do
    run_one "$file"
done < <(find "$ROOT/examples" -maxdepth 1 -type f -name '*.metta' | sort)

{
    printf '\n'
    printf 'Default PeTTa examples smoke:\n'
    printf '  total=%s ran=%s skipped=%s passed=%s failed=%s timed_out=%s\n' \
        "$total" "$ran" "$skipped" "$passed" "$failed" "$timed_out"
    printf '  log=%s\n' "$LOG"
} | tee -a "$LOG"

if [ "$failed" -gt 0 ] || [ "$timed_out" -gt 0 ]; then
    exit 1
fi
