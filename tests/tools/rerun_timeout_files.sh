#!/usr/bin/env bash
# Focused re-run of the 12 timeout rows from the translator survey at
# a longer timeout (default 300s) to distinguish "really slow under --he"
# from "non-terminating under --he".

set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
RUN_SH=${RUN_SH:-"$ROOT/run.sh"}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-300}
LIMIT_KB=${LIMIT_KB:-10485760}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}
STAMP=${STAMP:-$(date -u +%Y%m%dT%H%M%SZ)}
TSV=${TSV:-"$HE_LOG_DIR/he_translation_timeout_rerun_${TIMEOUT_SECONDS}s_${STAMP}.tsv"}
LOG=${LOG:-"$HE_LOG_DIR/he_translation_timeout_rerun_${STAMP}.log"}

ulimit -v "$LIMIT_KB"
mkdir -p "$HE_LOG_DIR"
: > "$LOG"

FILES='matespace2 matespacefast matespace peano holbenchmark hyperpose_primes scale peanofast patrick_iterate_quad nars_tuffy pln_roman invertpeanoplus'

printf 'source\tdefault_wall\tdefault_rss\tdefault_exit\the_wall\the_rss\the_exit\tratio_wall\treading\n' > "$TSV"

run_capture() {
    local err out rc
    err=$(mktemp)
    set +e
    out=$(/usr/bin/time -f '__TIME__ wall=%e rss_kb=%M exit=%x' \
            timeout "$TIMEOUT_SECONDS" "$@" 2>"$err")
    rc=$?
    set -e
    local time_line wall rss exit_field
    time_line=$(grep '^__TIME__' "$err" | tail -1)
    rm -f "$err"
    wall=$(printf '%s' "$time_line" | sed -nE 's/.*wall=([0-9.]+).*/\1/p')
    rss=$(printf '%s' "$time_line" | sed -nE 's/.*rss_kb=([0-9]+).*/\1/p')
    exit_field=$(printf '%s' "$time_line" | sed -nE 's/.*exit=([0-9]+).*/\1/p')
    : "${wall:=NA}" "${rss:=NA}" "${exit_field:=$rc}"
    printf '%s\t%s\t%s' "$wall" "$rss" "$exit_field"
}

portable_generated_for_base() {
    local base=$1
    local sequential="$GENERATED_DIR/${base}_he_sequential.metta"
    local legacy="$GENERATED_DIR/${base}_he.metta"
    if [ "$base" != hyperpose_primes ] && [ -f "$legacy" ]; then
        printf '%s\n' "$legacy"
        return 0
    fi
    if [ -f "$sequential" ]; then
        printf '%s\n' "$sequential"
        return 0
    fi
    if [ -f "$legacy" ]; then
        printf '%s\n' "$legacy"
        return 0
    fi
    return 1
}

for base in $FILES; do
    src="examples/${base}.metta"
    gen=$(portable_generated_for_base "$base" || true)
    if [ ! -f "$ROOT/$src" ]; then
        printf 'MISSING source %s\n' "$src" | tee -a "$LOG"
        continue
    fi
    if [ -z "$gen" ] || [ ! -f "$gen" ]; then
        printf 'MISSING generated portable translation for %s\n' "$base" | tee -a "$LOG"
        continue
    fi
    printf '\n>>> %s (timeout=%ss)\n' "$base" "$TIMEOUT_SECONDS" | tee -a "$LOG"

    def_pkt=$(run_capture "$RUN_SH" "$ROOT/$src" --silent)
    def_wall=$(printf '%s' "$def_pkt" | cut -f1)
    def_rss=$(printf '%s' "$def_pkt" | cut -f2)
    def_exit=$(printf '%s' "$def_pkt" | cut -f3)
    printf '  default: wall=%s rss=%s exit=%s\n' "$def_wall" "$def_rss" "$def_exit" | tee -a "$LOG"

    he_pkt=$(run_capture "$RUN_SH" --he "$gen" --silent)
    he_wall=$(printf '%s' "$he_pkt" | cut -f1)
    he_rss=$(printf '%s' "$he_pkt" | cut -f2)
    he_exit=$(printf '%s' "$he_pkt" | cut -f3)
    printf '  --he:    wall=%s rss=%s exit=%s\n' "$he_wall" "$he_rss" "$he_exit" | tee -a "$LOG"

    # Compute ratio safely.
    ratio=$(awk -v a="$he_wall" -v b="$def_wall" 'BEGIN{ if (b+0 > 0 && a != "NA") printf "%.2f", a/b; else printf "NA" }')

    # Reading: if both finished and --he ratio is reasonable → "perf gap"; if --he timed out and default fast → "non-termination"; else "heavy compute, --he slower".
    reading="-"
    if [ "$he_exit" = 124 ]; then
        if [ "$(awk -v d="$def_wall" 'BEGIN{print (d+0 < 1) ? 1 : 0}')" = 1 ]; then
            reading="non-termination under --he"
        else
            reading="--he too slow even at ${TIMEOUT_SECONDS}s"
        fi
    elif [ "$def_exit" = 0 ] && [ "$he_exit" = 0 ]; then
        reading="completed under both, ratio=${ratio}x"
    else
        reading="exit-mismatch default=$def_exit he=$he_exit"
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$src" "$def_wall" "$def_rss" "$def_exit" "$he_wall" "$he_rss" "$he_exit" "$ratio" "$reading" \
        >> "$TSV"
done

printf '\nTSV %s\n' "$TSV" | tee -a "$LOG"
