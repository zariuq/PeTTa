#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
PROLOG=${PROLOG:-swipl}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
TOP=${TOP:-30}
LOG_DIR=${LOG_DIR:-"$ROOT/.he-logs/profile_he_remaining"}

mkdir -p "$LOG_DIR"

usage() {
    cat <<'EOF'
Usage: tests/tools/profile_he_remaining.sh [--case NAME]

Profiles reduced HE repros with SWI's profiler and writes one log per case:
  tilepuzzle        tests/profile_repros/he_tilepuzzle_bfs_500.metta
  pln_roman         tests/profile_repros/he_pln_roman_step10.metta
  nars_tuffy        tests/profile_repros/he_nars_tuffy_step2.metta
  hyperpose_primes  tests/profile_repros/he_hyperpose_primes_once_reduced.metta

Environment:
  TIMEOUT_SECONDS   per-case profiling window in seconds (default: 120)
  TOP               show_profile top-N entries (default: 30)
  LOG_DIR           output directory (default: .he-logs/profile_he_remaining)
EOF
}

ONLY_CASE=${ONLY_CASE:-}
while [ $# -gt 0 ]; do
    case $1 in
        --case)
            ONLY_CASE=$2
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            printf 'unknown arg: %s\n' "$1" >&2
            exit 64
            ;;
    esac
done

CASES='
tilepuzzle tests/profile_repros/he_tilepuzzle_bfs_500.metta
pln_roman tests/profile_repros/he_pln_roman_step10.metta
nars_tuffy tests/profile_repros/he_nars_tuffy_step2.metta
hyperpose_primes tests/profile_repros/he_hyperpose_primes_once_reduced.metta
'

for entry in $CASES; do
    :
done

while read -r name file; do
    [ -n "${name:-}" ] || continue
    if [ -n "$ONLY_CASE" ] && [ "$ONLY_CASE" != "$name" ]; then
        continue
    fi

    abs_file="$ROOT/$file"
    log="$LOG_DIR/${name}.profile.txt"
    hard_timeout=$((TIMEOUT_SECONDS + 20))
    goal="use_module(library(prolog_profile)), use_module(library(time)), set_metta_profile(he), catch(retractall(silent(_)),_,true), assertz(silent(true)), (catch(profile(call_with_time_limit($TIMEOUT_SECONDS, load_metta_file('$abs_file', _))), time_limit_exceeded, (format('PROFILE_TIME_LIMIT_EXCEEDED~n', []), true))), show_profile([top($TOP)]), halt."

    {
        printf '== %s ==\n' "$name"
        printf 'file=%s\n' "$abs_file"
        printf 'profile_window=%ss hard_timeout=%ss top=%s\n' "$TIMEOUT_SECONDS" "$hard_timeout" "$TOP"
        if timeout "$hard_timeout" "$PROLOG" -q -s "$ROOT/src/metta.pl" -g "$goal"; then
            rc=0
        else
            rc=$?
        fi
        printf 'exit=%s\n' "$rc"
    } >"$log" 2>&1

    printf '%s\t%s\n' "$name" "$log"
done <<EOF
$CASES
EOF
