#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
PROLOG=${PROLOG:-swipl}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
LOG_DIR=${LOG_DIR:-"$ROOT/.he-logs/profile_he_remaining"}
CASE_FILE=${1:-tests/profile_repros/he_hyperpose_primes_once_reduced.metta}

mkdir -p "$LOG_DIR"

abs_file="$ROOT/$CASE_FILE"
base=$(basename "$CASE_FILE" .metta)
log="$LOG_DIR/${base}.threads.txt"
hard_timeout=$((TIMEOUT_SECONDS + 20))

goal="use_module(library(time)), set_metta_profile(he), catch(retractall(silent(_)),_,true), assertz(silent(true)), he_hyperpose_thread_profile_enable, catch(call_with_time_limit($TIMEOUT_SECONDS, load_metta_file('$abs_file', _)), time_limit_exceeded, (format('PROFILE_TIME_LIMIT_EXCEEDED~n', []), true)), he_hyperpose_thread_profile_report(user_output), halt."

{
    printf '== hyperpose_threads ==\n'
    printf 'file=%s\n' "$abs_file"
    printf 'profile_window=%ss hard_timeout=%ss\n' "$TIMEOUT_SECONDS" "$hard_timeout"
    if timeout "$hard_timeout" "$PROLOG" -q -s "$ROOT/src/metta.pl" -g "$goal"; then
        rc=0
    else
        rc=$?
    fi
    printf 'exit=%s\n' "$rc"
} >"$log" 2>&1

printf '%s\n' "$log"
