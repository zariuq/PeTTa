#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)

# shellcheck source=lib/he_classify.sh
. "$SCRIPT_DIR/lib/he_classify.sh"

if [ -n "${HE_CORPUS_ROOT:-}" ]; then
    CORPUS_ROOT=$HE_CORPUS_ROOT
elif [ -d "$ROOT/corpus" ]; then
    CORPUS_ROOT="$ROOT/corpus"
else
    printf 'ERROR: set HE_CORPUS_ROOT=/path/to/he-corpus, or provide %s/corpus.\n' "$ROOT" >&2
    exit 2
fi
RUN_SH=${RUN_SH:-"$ROOT/run.sh"}
HE_METTA_BIN=${HE_METTA_BIN:-$(command -v metta || true)}
HE_ORACLE_HOME=${HE_ORACLE_HOME:-"$ROOT/.he-home"}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
LIMIT_KB=${LIMIT_KB:-10485760}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
REPORT=${REPORT:-"$HE_LOG_DIR/petta_he_oracle_diff_$(date -u +%Y%m%dT%H%M%SZ).md"}
STRICT_ORACLE=${STRICT_ORACLE:-0}
ORACLE_LIMIT=${ORACLE_LIMIT:-0}

if [ -z "$HE_METTA_BIN" ]; then
    printf 'SKIP upstream HE oracle diff; set HE_METTA_BIN=/path/to/metta.\n'
    exit 0
fi

is_support_only() {
    case "$1" in
        */cetta_tests/spec_module_inventory.metta) return 0 ;;
        */cetta_tests/profile_he_prime_dependent_binders_compat.metta) return 0 ;;
        */cetta_tests/support/import_parse_fail/module.metta) return 0 ;;
        *) return 1 ;;
    esac
}

collect_files() {
    find "$CORPUS_ROOT" -type f -name '*.metta' | sort
}

mkdir -p "$(dirname -- "$REPORT")" "$HE_ORACLE_HOME"
{
    printf '# PeTTa --he Oracle Comparison\n\n'
    printf 'This is the low-level row report. Use `tests/run_he_corpus_bundle.sh`\n'
    printf 'for the human-facing conformance/support summary.\n\n'
    printf 'Corpus: `%s`\n\n' "$CORPUS_ROOT"
    printf 'Upstream HE: `%s`\n\n' "$HE_METTA_BIN"
    printf 'Upstream HE HOME: `%s`\n\n' "$HE_ORACLE_HOME"
    printf '| file | comparison | category | divergence | upstream HE | PeTTa --he |\n'
    printf '| --- | --- | --- | --- | --- | --- |\n'
} > "$REPORT"

total=0
skipped=0
processed=0
same=0
diff=0
declare -A cat_total=()
declare -A cat_same=()
declare -A cat_diff=()
categories=()

while IFS= read -r file; do
    total=$((total + 1))
    rel=${file#"$CORPUS_ROOT"/}
    if is_support_only "$file"; then
        skipped=$((skipped + 1))
        continue
    fi
    if [ "$ORACLE_LIMIT" -gt 0 ] && [ "$processed" -ge "$ORACLE_LIMIT" ]; then
        break
    fi
    processed=$((processed + 1))

    he_pair=$(run_capture he "$HE_METTA_BIN" "$file")
    petta_pair=$(run_capture petta "$RUN_SH" --he "$file" --silent)
    he_rc=${he_pair%%$'\t'*}
    he_out=${he_pair#*$'\t'}
    petta_rc=${petta_pair%%$'\t'*}
    petta_out=${petta_pair#*$'\t'}

    if [ "$he_rc" = "$petta_rc" ] && [ "$he_out" = "$petta_out" ]; then
        status=same
        same=$((same + 1))
    else
        status=diff
        diff=$((diff + 1))
    fi

    class_pair=$(classify_case "$rel" "$status" "$he_out" "$petta_out")
    category=${class_pair%%$'\t'*}
    divergence=${class_pair#*$'\t'}
    remember_category "$category" "$status"
    if [ "$status" = same ]; then
        comparison=exact
    else
        comparison=review
    fi

    printf '| `%s` | `%s` | `%s` | `%s` | `exit=%s %s` | `exit=%s %s` |\n' \
        "$rel" "$comparison" "$category" "$divergence" "$he_rc" "$he_out" "$petta_rc" "$petta_out" >> "$REPORT"
done < <(collect_files)

runnable=$((total - skipped))
{
    printf '\n## Category Summary\n\n'
    printf '| category | exact | review | total |\n'
    printf '| --- | ---: | ---: | ---: |\n'
    for category in "${categories[@]}"; do
        printf '| `%s` | %s | %s | %s |\n' \
            "$category" "${cat_same[$category]}" "${cat_diff[$category]}" "${cat_total[$category]}"
    done
    printf '\n## Totals\n\n'
    printf -- '- files seen: %s\n' "$total"
    printf -- '- skipped fixtures/admin probes: %s\n' "$skipped"
    printf -- '- processed rows: %s of %s non-skipped files\n' "$processed" "$runnable"
    printf -- '- exact output rows: %s\n' "$same"
    printf -- '- rows needing review/classification: %s\n' "$diff"
    printf 'REPORT %s\n' "$REPORT"
} | tee -a "$REPORT"

if [ "$STRICT_ORACLE" = 1 ]; then
    test "$diff" -eq 0
else
    exit 0
fi
