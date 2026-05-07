#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(cd -- "$SCRIPT_DIR/../.." && pwd)
CLASSIFY_SH="$ROOT/tests/lib/he_classify.sh"
SEVERITY_SH="$ROOT/tests/tools/generate_he_core_severity_tsv.sh"
TMP_LOG=$(mktemp "$ROOT/.he-logs/no_return_policy_guardrail.XXXXXX.log")
TMP_TSV=$(mktemp "$ROOT/.he-logs/no_return_policy_guardrail.XXXXXX.tsv")
cleanup() {
    rm -f "$TMP_LOG" "$TMP_TSV"
}
trap cleanup EXIT

# shellcheck source=../lib/he_classify.sh
source "$CLASSIFY_SH"

printf '%s\n' "$(upstream_only_kind cetta_tests/test_no_return_error.metta)"
printf 'UPSTREAM_QUIRK cetta_tests/test_no_return_error.metta\n' > "$TMP_LOG"
"$SEVERITY_SH" "$TMP_LOG" "$TMP_TSV"
cat "$TMP_TSV"
