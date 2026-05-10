#!/usr/bin/env bash
set -euo pipefail

usage() {
    cat <<'EOF'
Usage: tests/tools/diff_he_perf_counter_summaries.sh BEFORE.tsv AFTER.tsv [OUT.tsv]

Compares two he_perf_counter_summary.tsv files and writes a delta TSV.
Numeric columns are reported as AFTER - BEFORE. Ratio columns are shown as
floating deltas with three decimals. Non-numeric identity columns are copied
from the AFTER file when present, otherwise the BEFORE file.
EOF
}

if [ "${1:-}" = "-h" ] || [ "${1:-}" = "--help" ]; then
    usage
    exit 0
fi

if [ $# -lt 2 ] || [ $# -gt 3 ]; then
    usage >&2
    exit 64
fi

BEFORE=$1
AFTER=$2
OUT=${3:-}

if [ -z "$OUT" ]; then
    OUT=$(dirname -- "$AFTER")/he_perf_counter_summary_diff.tsv
fi

TMP_ROWS=$(mktemp "$(dirname -- "$OUT")/.he_perf_counter_diff_rows.XXXXXX")
trap 'rm -f "$TMP_ROWS"' EXIT

awk -F '\t' -v OFS='\t' '
function is_number(value) {
    return value ~ /^-?[0-9]+(\.[0-9]+)?$/
}
FNR == 1 {
    if (NR == FNR) {
        cols = NF
        for (i = 1; i <= NF; i++) {
            header[i] = $i
            if ($i == "case") case_col = i
        }
    }
    next
}
NR == FNR {
    case_name = $case_col
    for (i = 1; i <= NF; i++) before[case_name, i] = $i
    seen_before[case_name] = 1
    next
}
{
    case_name = $case_col
    for (i = 1; i <= NF; i++) after[case_name, i] = $i
    seen_after[case_name] = 1
    next
}
END {
    print "case", "status", "exit_before", "exit_after", "compiled_collections_delta", "compiled_raw_rows_delta", "compiled_visible_rows_delta", "raw_per_collection_delta", "visible_per_collection_delta", "typed_calls_delta", "typed_replays_delta", "replay_rate_delta", "collect_calls_delta", "collect_rows_delta", "bind_calls_delta", "bind_rows_delta", "once_calls_delta", "count_calls_delta", "count_rows_delta", "fold_calls_delta", "fold_rows_delta", "space_exact_calls_delta", "space_exact_hits_delta"
    for (case_name in seen_before) seen[case_name] = 1
    for (case_name in seen_after) seen[case_name] = 1
    for (case_name in seen) {
        if (seen_before[case_name] && seen_after[case_name]) status = "both"
        else if (seen_after[case_name]) status = "after_only"
        else status = "before_only"
        exit_before = seen_before[case_name] ? before[case_name, 2] : ""
        exit_after = seen_after[case_name] ? after[case_name, 2] : ""
        printf "%s\t%s\t%s\t%s", case_name, status, exit_before, exit_after
        for (i = 3; i <= cols; i++) {
            before_val = seen_before[case_name] ? before[case_name, i] : ""
            after_val = seen_after[case_name] ? after[case_name, i] : ""
            if (is_number(before_val) && is_number(after_val)) {
                if (before_val ~ /\./ || after_val ~ /\./) {
                    printf "\t%.3f", after_val - before_val
                } else {
                    printf "\t%d", after_val - before_val
                }
            } else if (before_val == "" && is_number(after_val)) {
                if (after_val ~ /\./) printf "\t%.3f", after_val + 0
                else printf "\t%d", after_val + 0
            } else if (after_val == "" && is_number(before_val)) {
                if (before_val ~ /\./) printf "\t%.3f", 0 - before_val
                else printf "\t%d", 0 - before_val
            } else {
                printf "\t"
            }
        }
        printf "\n"
    }
}
' "$BEFORE" "$AFTER" > "$TMP_ROWS"

{
    head -n 1 "$TMP_ROWS"
    tail -n +2 "$TMP_ROWS" | sort
} > "$OUT"

printf '%s\n' "$OUT"
