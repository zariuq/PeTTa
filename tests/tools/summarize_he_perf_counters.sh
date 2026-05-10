#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
LOG_DIR=${LOG_DIR:-"$ROOT/.he-logs/profile_he_remaining"}
OUT=${OUT:-"$LOG_DIR/he_perf_counter_summary.tsv"}

usage() {
    cat <<'EOF'
Usage: tests/tools/summarize_he_perf_counters.sh

Reads profile_he_remaining/*.profile.txt counter blocks and writes a TSV summary.

Environment:
  LOG_DIR  directory containing *.profile.txt logs
  OUT      output TSV path
EOF
}

if [ "${1:-}" = "-h" ] || [ "${1:-}" = "--help" ]; then
    usage
    exit 0
fi

mkdir -p "$(dirname -- "$OUT")"
TMP_ROWS=$(mktemp "$LOG_DIR/.he_perf_counter_summary_rows.XXXXXX")
trap 'rm -f "$TMP_ROWS"' EXIT

for log in "$LOG_DIR"/*.profile.txt; do
    [ -f "$log" ] || continue
    case_name=$(basename "$log" .profile.txt)
    awk -v case_name="$case_name" '
        function counter(name) {
            return (name in counts) ? counts[name] : 0
        }
        function ratio(num, den) {
            if (den == 0) return "0.000"
            return sprintf("%.3f", num / den)
        }
        BEGIN {
            in_block = 0
            exit_code = ""
        }
        /^HE_PERF_COUNTERS_BEGIN$/ { in_block = 1; next }
        /^HE_PERF_COUNTERS_END$/ { in_block = 0; next }
        /^exit=/ {
            split($0, a, "=")
            exit_code = a[2]
            next
        }
        in_block && NF >= 2 {
            counts[$1] = $2
        }
        END {
            compiled = counter("compiled_equation_goal_result_collections")
            raw = counter("compiled_equation_goal_raw_rows")
            visible = counter("compiled_equation_goal_visible_rows")
            typed_calls = counter("typed_visible_or_all_calls")
            typed_replays = counter("typed_visible_or_all_replays")
            collect_calls = counter("collect_visible_results_calls")
            collect_rows = counter("collect_visible_results_rows")
            bind_calls = counter("bind_visible_results_calls")
            bind_rows = counter("bind_visible_results_rows")
            once_calls = counter("once_visible_result_calls")
            count_calls = counter("count_visible_results_calls")
            count_rows = counter("count_visible_results_rows")
            fold_calls = counter("fold_visible_results_calls")
            fold_rows = counter("fold_visible_results_rows")
            space_exact_calls = counter("space_exact_member_calls")
            space_exact_hits = counter("space_exact_member_hits")
            printf "%s\t%s\t%d\t%d\t%d\t%s\t%s\t%d\t%d\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
                   case_name,
                   exit_code,
                   compiled,
                   raw,
                   visible,
                   ratio(raw, compiled),
                   ratio(visible, compiled),
                   typed_calls,
                   typed_replays,
                   ratio(typed_replays, typed_calls),
                   collect_calls,
                   collect_rows,
                   bind_calls,
                   bind_rows,
                   once_calls,
                   count_calls,
                   count_rows,
                   fold_calls,
                   fold_rows,
                   space_exact_calls,
                   space_exact_hits
        }
    ' "$log"
done | sort > "$TMP_ROWS"

{
    printf 'case\texit\tcompiled_collections\tcompiled_raw_rows\tcompiled_visible_rows\traw_per_collection\tvisible_per_collection\ttyped_calls\ttyped_replays\treplay_rate\tcollect_calls\tcollect_rows\tbind_calls\tbind_rows\tonce_calls\tcount_calls\tcount_rows\tfold_calls\tfold_rows\tspace_exact_calls\tspace_exact_hits\n'
    cat "$TMP_ROWS"
} > "$OUT"

printf '%s\n' "$OUT"
