#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
HYPERON_ROOT=$(cd -- "$ROOT/.." && pwd)
RUN_SH=${RUN_SH:-"$ROOT/run.sh"}
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
INVENTORY_TSV=${INVENTORY_TSV:-"$HE_LOG_DIR/he_translation_inventory.tsv"}
STAMP=${STAMP:-$(date -u +%Y%m%dT%H%M%SZ)_$$}
OUT_TSV=${OUT_TSV:-"$HE_LOG_DIR/generated_he_portability_${STAMP}.tsv"}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-30}
LIMIT_KB=${LIMIT_KB:-10485760}
ONLY_PATTERN=${ONLY_PATTERN:-}
LIMIT=${LIMIT:-0}

if [ -x "$HYPERON_ROOT/CeTTa/cetta" ]; then
    CETTA_BIN=${CETTA_BIN:-"$HYPERON_ROOT/CeTTa/cetta"}
else
    CETTA_BIN=${CETTA_BIN:-$(command -v cetta || true)}
fi

HE_METTA_BIN=${HE_METTA_BIN:-$(command -v metta || true)}

HE_ORACLE_HOME=${HE_ORACLE_HOME:-"$ROOT/.he-home"}
TRANSLATOR_HELPER_RE='assertEqualToEval|assertEqualToResult|assertAlphaEqualToResult|assertEqualMsg|assertEqualToResultMsg|assertAlphaEqualMsg|assertAlphaEqualToResultMsg|assertIncludes|(^|[[:space:](!])test([[:space:])])'

usage() {
    cat <<'EOF'
Usage:
  check_generated_he_portability.sh [--only <glob-fragment>] [--limit <n>]

Runs generated examples under:
  1. PeTTa --he
  2. CeTTa --lang he
  3. upstream HE oracle

Outputs a TSV row per generated file with a portability classification.
EOF
}

while [ $# -gt 0 ]; do
    case $1 in
        --only) ONLY_PATTERN=$2; shift 2 ;;
        --limit) LIMIT=$2; shift 2 ;;
        -h|--help) usage; exit 0 ;;
        *) printf 'unknown arg: %s\n' "$1" >&2; exit 64 ;;
    esac
done

mkdir -p "$HE_LOG_DIR" "$HE_ORACLE_HOME"

normalize_output() {
    sed -e '/^MORK init:/d' \
        -e 's/[[:space:]]*$//'
}

run_capture() {
    local label=$1
    shift
    local out rc
    set +e
    if [ "$label" = upstream ]; then
        out=$(ulimit -v "$LIMIT_KB" && HOME="$HE_ORACLE_HOME" timeout "$TIMEOUT_SECONDS" "$@" 2>&1)
    else
        out=$(ulimit -v "$LIMIT_KB" && timeout "$TIMEOUT_SECONDS" "$@" 2>&1)
    fi
    rc=$?
    set -e
    printf '%s\t%s\n' "$rc" "$(printf '%s\n' "$out" | normalize_output | sed ':a;N;$!ba;s/\n/\\n/g')"
}

file_mode() {
    case $1 in
        *_he_parallel.metta) printf '%s\n' parallel ;;
        *_he_sequential.metta) printf '%s\n' sequential ;;
        *_he.metta) printf '%s\n' default ;;
        *) printf '%s\n' unknown ;;
    esac
}

has_translator_helper_surface() {
    grep -Eq "$TRANSLATOR_HELPER_RE" "$1"
}

source_from_header() {
    sed -n 's/^; Source: //p' "$1" | head -1
}

inventory_category() {
    local source=$1
    if [ -n "$source" ] && [ -f "$INVENTORY_TSV" ]; then
        awk -F '\t' -v source="$source" '$1 == source { print $2; found=1; exit } END { if (!found) print "" }' "$INVENTORY_TSV"
    fi
}

classify_row() {
    local file=$1
    local mode=$2
    local has_helper=$3
    local petta_rc=$4
    local cetta_rc=$5
    local upstream_rc=$6
    local petta_out=$7
    local cetta_out=$8
    local upstream_out=$9

    if [ "$petta_rc" != 0 ]; then
        printf '%s\t%s\n' petta_he_failure 'PeTTa --he did not complete cleanly'
        return
    fi

    if [ -z "$CETTA_BIN" ] || [ -z "$HE_METTA_BIN" ]; then
        printf '%s\t%s\n' infra_missing 'CeTTa or upstream HE oracle binary is missing'
        return
    fi

    if [ "$cetta_rc" = 0 ] && [ "$upstream_rc" = 0 ] &&
       [ "$petta_out" = "$cetta_out" ] && [ "$petta_out" = "$upstream_out" ]; then
        printf '%s\t%s\n' portable_exact 'exact portable result across PeTTa, CeTTa, and upstream HE'
        return
    fi

    if [ "$has_helper" = 1 ] &&
       [ "$cetta_rc" = 0 ] && [ "$upstream_rc" = 0 ] &&
       printf '%s\n' "$cetta_out" | grep -Eq "$TRANSLATOR_HELPER_RE" &&
       printf '%s\n' "$upstream_out" | grep -Eq "$TRANSLATOR_HELPER_RE"; then
        printf '%s\t%s\n' translator_helper_surface 'translated file uses a source-compatibility or assertion helper; CeTTa/upstream leave it as data unless the helper is supplied'
        return
    fi

    if [ "$mode" = parallel ]; then
        printf '%s\t%s\n' parallel_runtime_lane 'parallel hyperpose lane is not claimed portable pure HE'
        return
    fi

    case "$cetta_rc:$upstream_rc" in
        124:124|137:137|124:137|137:124)
            printf '%s\t%s\n' timeout_elsewhere 'CeTTa and upstream both timed out'
            return
            ;;
    esac

    if [ "$cetta_rc" != 0 ] && [ "$upstream_rc" != 0 ]; then
        printf '%s\t%s\n' engine_failure_elsewhere 'CeTTa and upstream both failed non-cleanly'
        return
    fi

    if [ "$cetta_rc" = 0 ] && [ "$upstream_rc" = 0 ] && [ "$cetta_out" = "$upstream_out" ]; then
        printf '%s\t%s\n' same_elsewhere_diff_from_petta 'CeTTa and upstream agree with each other but differ from PeTTa --he'
        return
    fi

    if [ "$cetta_rc" = 0 ] && [ "$upstream_rc" = 0 ]; then
        printf '%s\t%s\n' cross_engine_split 'CeTTa and upstream both ran, but do not agree exactly'
        return
    fi

    if [ "$cetta_rc" = 0 ] || [ "$upstream_rc" = 0 ]; then
        printf '%s\t%s\n' one_engine_only 'exactly one non-PeTTa engine completed cleanly'
        return
    fi

    printf '%s\t%s\n' unresolved_diff 'nontrivial portability mismatch; inspect outputs'
}

printf 'file\tmode\thas_translator_helper_surface\tpetta_rc\tcetta_rc\tupstream_rc\tclass\tnotes\tpetta_out\tcetta_out\tupstream_out\n' > "$OUT_TSV"

count=0
shopt -s nullglob
for file in "$GENERATED_DIR"/*_he.metta "$GENERATED_DIR"/*_he_sequential.metta "$GENERATED_DIR"/*_he_parallel.metta; do
    base=$(basename -- "$file")
    if [ -n "$ONLY_PATTERN" ] && [[ "$base" != *"$ONLY_PATTERN"* ]]; then
        continue
    fi
    count=$((count + 1))
    if [ "$LIMIT" -gt 0 ] && [ "$count" -gt "$LIMIT" ]; then
        break
    fi

    mode=$(file_mode "$file")
    if has_translator_helper_surface "$file"; then
        has_helper=1
    else
        has_helper=0
    fi

    source=$(source_from_header "$file")
    survey_category=$(inventory_category "$source")
    if [ -n "$survey_category" ] && [ "$survey_category" != translated_passes ]; then
        printf '%s\t%s\t%s\t-\t-\t-\t%s\t%s\t-\t-\t-\n' \
            "$file" "$mode" "$has_helper" \
            survey_out_of_scope "inventory category: $survey_category for $source" >> "$OUT_TSV"
        continue
    fi

    petta_pair=$(run_capture petta "$RUN_SH" --he "$file" --silent)
    petta_rc=${petta_pair%%$'\t'*}
    petta_out=${petta_pair#*$'\t'}

    if [ -n "$CETTA_BIN" ]; then
        cetta_pair=$(run_capture cetta "$CETTA_BIN" --lang he "$file")
        cetta_rc=${cetta_pair%%$'\t'*}
        cetta_out=${cetta_pair#*$'\t'}
    else
        cetta_rc=127
        cetta_out='CETTA_BIN missing'
    fi

    if [ -n "$HE_METTA_BIN" ]; then
        upstream_pair=$(run_capture upstream "$HE_METTA_BIN" "$file")
        upstream_rc=${upstream_pair%%$'\t'*}
        upstream_out=${upstream_pair#*$'\t'}
    else
        upstream_rc=127
        upstream_out='HE_METTA_BIN missing'
    fi

    class_pair=$(classify_row "$file" "$mode" "$has_helper" \
        "$petta_rc" "$cetta_rc" "$upstream_rc" \
        "$petta_out" "$cetta_out" "$upstream_out")
    class_name=${class_pair%%$'\t'*}
    notes=${class_pair#*$'\t'}

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$file" "$mode" "$has_helper" \
        "$petta_rc" "$cetta_rc" "$upstream_rc" \
        "$class_name" "$notes" \
        "$petta_out" "$cetta_out" "$upstream_out" >> "$OUT_TSV"
done

printf 'Wrote %s\n' "$OUT_TSV"
