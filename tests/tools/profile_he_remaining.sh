#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
PROLOG=${PROLOG:-swipl}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
TOP=${TOP:-30}
PROFILE_SWI=${PROFILE_SWI:-0}
LOG_DIR=${LOG_DIR:-"$ROOT/.he-logs/profile_he_remaining"}

mkdir -p "$LOG_DIR"

usage() {
    cat <<'EOF'
Usage: tests/tools/profile_he_remaining.sh [--case NAME]

Profiles reduced HE repros with SWI's profiler and writes one log per case:
  tilepuzzle        tests/profile_repros/he_tilepuzzle_bfs_500_witness.metta
  tilepuzzle_unseeded tests/profile_repros/he_tilepuzzle_unseeded_bfs_500_witness.metta
  tilepuzzle_full   tests/profile_repros/he_tilepuzzle_full_measure.metta
  tilepuzzle_imported tests/profile_repros/he_tilepuzzle_imported_bfs_500_witness.metta
  tilepuzzle_imported_large tests/profile_repros/he_tilepuzzle_imported_bfs_50000_witness.metta
  peano             tests/profile_repros/he_peano_demo_50_witness.metta
  matespacefast     tests/profile_repros/he_matespacefast_translated_demo_6_measure.metta
  matespacefast_medium tests/profile_repros/he_matespacefast_translated_demo_10_measure.metta
  matespacefast_large tests/profile_repros/he_matespacefast_translated_demo_16_measure.metta
  holbenchmark      tests/profile_repros/he_holbenchmark_witness.metta
  holbenchmark_full tests/profile_repros/he_holbenchmark_full_measure.metta
  holbenchmark_mapflat tests/profile_repros/he_holbenchmark_mapflat_range_measure.metta
  holbenchmark_mapflat_mid tests/profile_repros/he_holbenchmark_mapflat_mid_measure.metta
  holbenchmark_mapflat_large tests/profile_repros/he_holbenchmark_mapflat_large_measure.metta
  holbenchmark_mapflat_full tests/profile_repros/he_holbenchmark_mapflat_full_measure.metta
  holbenchmark_fold_nested tests/profile_repros/he_holbenchmark_fold_nested_measure.metta
  holbenchmark_fold_nested_mid tests/profile_repros/he_holbenchmark_fold_nested_mid_measure.metta
  holbenchmark_fold_nested_large tests/profile_repros/he_holbenchmark_fold_nested_large_measure.metta
  holbenchmark_fold_nested_full tests/profile_repros/he_holbenchmark_fold_nested_full_measure.metta
  holbenchmark_recursive tests/profile_repros/he_holbenchmark_recursive_call_measure.metta
  holbenchmark_apply_many_full tests/profile_repros/he_holbenchmark_apply_many_full_measure.metta
  holbenchmark_poly_full tests/profile_repros/he_holbenchmark_poly_full_measure.metta
  nars_tuffy        tests/profile_repros/he_nars_tuffy_smallkb_witness.metta
  pln_roman         tests/profile_repros/he_pln_roman_step10.metta
  hyperpose_primes  tests/profile_repros/he_hyperpose_primes_once_reduced.metta
  prime_find_divisor tests/profile_repros/he_prime_find_divisor_single.metta

Environment:
  TIMEOUT_SECONDS   per-case profiling window in seconds (default: 120)
  TOP               show_profile top-N entries when PROFILE_SWI=1 (default: 30)
  PROFILE_SWI       1 to wrap the run in SWI's profiler, 0 for counter-first runs
                    (default: 0)
  LOG_DIR           output directory (default: .he-logs/profile_he_remaining)

Each profile log includes an HE runtime counter report between:
  HE_PERF_COUNTERS_BEGIN
  HE_PERF_COUNTERS_END
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
tilepuzzle tests/profile_repros/he_tilepuzzle_bfs_500_witness.metta
tilepuzzle_unseeded tests/profile_repros/he_tilepuzzle_unseeded_bfs_500_witness.metta
tilepuzzle_full tests/profile_repros/he_tilepuzzle_full_measure.metta
tilepuzzle_imported tests/profile_repros/he_tilepuzzle_imported_bfs_500_witness.metta
tilepuzzle_imported_large tests/profile_repros/he_tilepuzzle_imported_bfs_50000_witness.metta
peano tests/profile_repros/he_peano_demo_50_witness.metta
matespacefast tests/profile_repros/he_matespacefast_translated_demo_6_measure.metta
matespacefast_medium tests/profile_repros/he_matespacefast_translated_demo_10_measure.metta
matespacefast_large tests/profile_repros/he_matespacefast_translated_demo_16_measure.metta
holbenchmark tests/profile_repros/he_holbenchmark_witness.metta
holbenchmark_full tests/profile_repros/he_holbenchmark_full_measure.metta
holbenchmark_mapflat tests/profile_repros/he_holbenchmark_mapflat_range_measure.metta
holbenchmark_mapflat_mid tests/profile_repros/he_holbenchmark_mapflat_mid_measure.metta
holbenchmark_mapflat_large tests/profile_repros/he_holbenchmark_mapflat_large_measure.metta
holbenchmark_mapflat_full tests/profile_repros/he_holbenchmark_mapflat_full_measure.metta
holbenchmark_fold_nested tests/profile_repros/he_holbenchmark_fold_nested_measure.metta
holbenchmark_fold_nested_mid tests/profile_repros/he_holbenchmark_fold_nested_mid_measure.metta
holbenchmark_fold_nested_large tests/profile_repros/he_holbenchmark_fold_nested_large_measure.metta
holbenchmark_fold_nested_full tests/profile_repros/he_holbenchmark_fold_nested_full_measure.metta
holbenchmark_recursive tests/profile_repros/he_holbenchmark_recursive_call_measure.metta
holbenchmark_apply_many_full tests/profile_repros/he_holbenchmark_apply_many_full_measure.metta
holbenchmark_poly_full tests/profile_repros/he_holbenchmark_poly_full_measure.metta
nars_tuffy tests/profile_repros/he_nars_tuffy_smallkb_witness.metta
pln_roman tests/profile_repros/he_pln_roman_step10.metta
hyperpose_primes tests/profile_repros/he_hyperpose_primes_once_reduced.metta
prime_find_divisor tests/profile_repros/he_prime_find_divisor_single.metta
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
    run_body="catch(load_metta_file('$abs_file', _), Err, (format('PROFILE_EXCEPTION\\t~q~n', [Err]), true))"
    timed_run="catch((catch(call_with_time_limit($TIMEOUT_SECONDS, $run_body), time_limit_exceeded, (format('PROFILE_TIME_LIMIT_EXCEEDED~n', []), true))), unwind(halt(Code)), (format('PROFILE_UNWIND_HALT\\t~w~n', [Code]), true))"
    if [ "$PROFILE_SWI" = "1" ]; then
        goal="use_module(library(prolog_profile)), use_module(library(time)), catch(retractall(silent(_)),_,true), assertz(silent(true)), set_metta_profile(he), he_perf_counters_enable, profile($timed_run), show_profile([top($TOP)]), he_perf_counters_report(user_output), halt."
    else
        goal="use_module(library(time)), catch(retractall(silent(_)),_,true), assertz(silent(true)), set_metta_profile(he), he_perf_counters_enable, $timed_run, he_perf_counters_report(user_output), halt."
    fi

    {
        printf '== %s ==\n' "$name"
        printf 'file=%s\n' "$abs_file"
        printf 'profile_window=%ss hard_timeout=%ss top=%s profile_swi=%s\n' "$TIMEOUT_SECONDS" "$hard_timeout" "$TOP" "$PROFILE_SWI"
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
