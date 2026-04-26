#!/usr/bin/env bash
# Translator-first PeTTa→HE examples survey + benchmark.
#
# For each examples/*.metta (maxdepth 1):
#   1. Run default PeTTa, capture wall/rss/exit.
#   2. If translation-eligible: run translator, run --he, capture
#      wall/rss/exit.
#   3. Classify the row using the vocabulary from the brief at
#      tmp/hepetta_examples_translation_bench_instructions_20260425.md
#      (translated_passes, translator_gap_*, he_runtime_gap_*,
#      petta_specific_no_translation, external_or_interactive,
#      already_he, default_source_fails).
#
# Outputs:
#   .he-logs/he_translation_inventory.tsv
#   .he-logs/he_translation_bench.tsv
#   .he-logs/he_translation_gaps/<base>.{he-stderr,he-stdout,translated}
#
# Translator commands recorded per-row so every _he.metta is reproducible.

set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
RUN_SH=${RUN_SH:-"$ROOT/run.sh"}
TRANSLATE_SH=${TRANSLATE_SH:-/home/zar/claude/hyperon/translators/translate.sh}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
LIMIT_KB=${LIMIT_KB:-10485760}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}
INVENTORY=${INVENTORY:-"$HE_LOG_DIR/he_translation_inventory.tsv"}
BENCH=${BENCH:-"$HE_LOG_DIR/he_translation_bench.tsv"}
GAPS_DIR=${GAPS_DIR:-"$HE_LOG_DIR/he_translation_gaps"}
STAMP=${STAMP:-$(date -u +%Y%m%dT%H%M%SZ)}
LOG=${LOG:-"$HE_LOG_DIR/he_translation_survey_${STAMP}.log"}

LIMIT=${LIMIT:-0}        # 0 = no cap; positive = stop after that many runs
ONLY_PATTERN=${ONLY_PATTERN:-}
RESUME=${RESUME:-0}      # 1 = skip rows already present in INVENTORY

while [ $# -gt 0 ]; do
    case $1 in
        --limit)   LIMIT=$2; shift 2 ;;
        --only)    ONLY_PATTERN=$2; shift 2 ;;
        --resume)  RESUME=1; shift ;;
        -h|--help) sed -n '2,32p' "$0"; exit 0 ;;
        *) printf 'unknown arg: %s\n' "$1" >&2; exit 64 ;;
    esac
done

if [ "$RESUME" != 1 ] && [ "${HE_SURVEY_OVERWRITE:-0}" != 1 ] &&
   { [ -n "$ONLY_PATTERN" ] || [ "$LIMIT" != 0 ]; }; then
    INVENTORY="$HE_LOG_DIR/he_translation_inventory_subset_${STAMP}.tsv"
    BENCH="$HE_LOG_DIR/he_translation_bench_subset_${STAMP}.tsv"
    LOG="$HE_LOG_DIR/he_translation_survey_subset_${STAMP}.log"
fi

ulimit -v "$LIMIT_KB"
mkdir -p "$HE_LOG_DIR" "$GENERATED_DIR" "$GAPS_DIR"
: > "$LOG"

if [ "$RESUME" = 1 ] && [ -s "$INVENTORY" ]; then
    # Build resume set from existing inventory (column 1).
    declare -A RESUME_DONE=()
    while IFS=$'\t' read -r src _; do
        [ "$src" = source ] && continue
        RESUME_DONE[$src]=1
    done < "$INVENTORY"
    printf 'RESUME mode: skipping %s already-processed rows\n' "${#RESUME_DONE[@]}" | tee -a "$LOG"
else
    # Headers (overwrite for fresh runs).
    printf 'source\tcategory\ttranslated\tdefault_exit\the_exit\treason\tnext_action\n' > "$INVENTORY"
    printf 'source\ttranslated\tdefault_wall\tdefault_rss\the_wall\the_rss\tratio_wall\tcategory\tnotes\n' > "$BENCH"
    declare -A RESUME_DONE=()
fi

# ------------------------------------------------------------------
# Skip lists
# ------------------------------------------------------------------

# Already_he: filename-prefix he_*.metta is excluded by glob below.
EXTERNAL_OR_INTERACTIVE='greedy_chess.metta repl.metta llm_cities.metta torch.metta git_import.metta git_import2.metta python.metta python_import.metta'

PETTA_SPECIFIC='translatorrule.metta translatorrule_fib.metta translatorrule_for.metta translatepredicate.metta streamops.metta metta4_streams.metta mutex_and_transaction.metta state.metta nilbc.metta metta4_prog.metta prologimport.metta myinterpreter.metta selfprog.metta smartdispatch.metta builin_types.metta parametric_types.metta recursive_types.metta meta_types.metta types_dependent.metta types_nondet.metta mettaset.metta spaces.metta spaces_find.metta spaces_removeallatoms.metta spaces_succeedspredicate.metta'

# Whether a given basename is in a space-separated list.
in_list() {
    local needle=$1; shift
    local hay=$1
    case " $hay " in
        *" $needle "*) return 0 ;;
        *)             return 1 ;;
    esac
}

# ------------------------------------------------------------------
# Capture helpers
# ------------------------------------------------------------------

# Captures: wall (s, %e), max RSS (KB, %M), exit (%x).
# stdout is captured separately for assertion/error inspection.
run_capture() {
    local label=$1
    shift
    local err
    err=$(mktemp)
    local out
    set +e
    out=$(/usr/bin/time -f '__TIME__ wall=%e rss_kb=%M exit=%x' \
            timeout "$TIMEOUT_SECONDS" "$@" 2>"$err")
    local cmd_rc=$?
    set -e
    local time_line
    time_line=$(grep '^__TIME__' "$err" | tail -1)
    local stderr_clean
    stderr_clean=$(grep -v '^__TIME__' "$err" || true)
    rm -f "$err"
    # Field-extract from time line.
    local wall rss exit_field
    wall=$(printf '%s' "$time_line" | sed -nE 's/.*wall=([0-9.]+).*/\1/p')
    rss=$(printf '%s' "$time_line" | sed -nE 's/.*rss_kb=([0-9]+).*/\1/p')
    exit_field=$(printf '%s' "$time_line" | sed -nE 's/.*exit=([0-9]+).*/\1/p')
    : "${wall:=NA}" "${rss:=NA}" "${exit_field:=$cmd_rc}"
    # Returns: rc<TAB>wall<TAB>rss<TAB>stdout<\037>stderr  (\037 separates)
    # We use \037 (US) since output may contain newlines/tabs.
    printf '%s\t%s\t%s\t%s\037%s' \
        "$exit_field" "$wall" "$rss" "$out" "$stderr_clean"
}

# Detect assertion failures the same way smoke does.
has_assert_failure() {
    printf '%s\n' "$1" | grep -qE '❌|Assertion failed:|IncorrectNumberOfArguments|BadType|TypeMismatch'
}

# ------------------------------------------------------------------
# Per-file processing
# ------------------------------------------------------------------

processed=0
classify_and_record() {
    local source=$1
    local rel=${source#"$ROOT"/}
    local base
    base=$(basename -- "$source" .metta)
    local generated="$GENERATED_DIR/${base}_he.metta"

    # Apply --only filter if set.
    if [ -n "$ONLY_PATTERN" ] && [[ "$rel" != *"$ONLY_PATTERN"* ]]; then
        return
    fi

    # Apply --resume: skip already-processed rows.
    if [ -n "${RESUME_DONE[$rel]:-}" ]; then
        return
    fi

    local fname
    fname=$(basename -- "$source")

    # Bucket 1 — already_he (skip)
    case $fname in he_*.metta)
        printf '%s\talready_he\t-\t-\t-\tHE-style example; covered by run_he_profile_suite.sh\t-\n' \
            "$rel" >> "$INVENTORY"
        printf 'SKIP[already_he] %s\n' "$rel" | tee -a "$LOG"
        return
    esac

    # Bucket 2 — external_or_interactive (skip)
    if in_list "$fname" "$EXTERNAL_OR_INTERACTIVE"; then
        printf '%s\texternal_or_interactive\t-\t-\t-\tnetwork/LLM/PyTorch/REPL/UI/Python bridge\t-\n' \
            "$rel" >> "$INVENTORY"
        printf 'SKIP[external_or_interactive] %s\n' "$rel" | tee -a "$LOG"
        return
    fi

    # Bucket 3 — petta_specific (skip translation, classify)
    if in_list "$fname" "$PETTA_SPECIFIC"; then
        printf '%s\tpetta_specific_no_translation\t-\t-\t-\tdeliberately PeTTa-only construct\t-\n' \
            "$rel" >> "$INVENTORY"
        printf 'SKIP[petta_specific] %s\n' "$rel" | tee -a "$LOG"
        return
    fi

    # ----- Run default PeTTa -----
    local default_pkt default_rc default_wall default_rss default_stdout default_stderr
    default_pkt=$(run_capture petta "$RUN_SH" "$source" --silent)
    default_rc=${default_pkt%%$'\t'*}
    local rest1=${default_pkt#*$'\t'}
    default_wall=${rest1%%$'\t'*}
    local rest2=${rest1#*$'\t'}
    default_rss=${rest2%%$'\t'*}
    local rest3=${rest2#*$'\t'}
    default_stdout=${rest3%%$'\037'*}
    default_stderr=${rest3#*$'\037'}

    # If default PeTTa fails OR prints assertion-failure marker,
    # classify default_source_fails and stop.
    if [ "$default_rc" != 0 ] || has_assert_failure "$default_stdout" \
                              || has_assert_failure "$default_stderr"; then
        printf '%s\tdefault_source_fails\t-\t%s\t-\toriginal PeTTa run failed (rc=%s)\tinvestigate before claiming HE compat\n' \
            "$rel" "$default_rc" "$default_rc" >> "$INVENTORY"
        printf 'SKIP[default_source_fails] %s rc=%s\n' "$rel" "$default_rc" | tee -a "$LOG"
        return
    fi

    # ----- Translate -----
    local trans_log="$GAPS_DIR/${base}.translate.stderr"
    if ! "$TRANSLATE_SH" petta2he "$source" "$generated" >"$GAPS_DIR/${base}.translate.stdout" 2>"$trans_log"; then
        printf '%s\ttranslator_gap_core\t-\t%s\t-\ttranslator command failed; see %s\tflag for petta_to_he.pl\n' \
            "$rel" "$default_rc" "$trans_log" >> "$INVENTORY"
        printf 'GAP[translator_failed] %s\n' "$rel" | tee -a "$LOG"
        return
    fi
    rm -f "$GAPS_DIR/${base}.translate.stdout" "$trans_log"

    local rel_gen=${generated#"$ROOT"/}

    # ----- Run --he on translated output -----
    local he_pkt he_rc he_wall he_rss he_stdout he_stderr
    he_pkt=$(run_capture he "$RUN_SH" --he "$generated" --silent)
    he_rc=${he_pkt%%$'\t'*}
    rest1=${he_pkt#*$'\t'}
    he_wall=${rest1%%$'\t'*}
    rest2=${rest1#*$'\t'}
    he_rss=${rest2%%$'\t'*}
    rest3=${rest2#*$'\t'}
    he_stdout=${rest3%%$'\037'*}
    he_stderr=${rest3#*$'\037'}

    # ----- Classify -----
    local category reason next_action
    if [ "$he_rc" = 0 ] && ! has_assert_failure "$he_stdout" && ! has_assert_failure "$he_stderr"; then
        category=translated_passes
        reason='translator output runs cleanly under --he'
        next_action='-'
    else
        # Some shape of failure. Distinguish by output signal.
        # `IncorrectNumberOfArguments` on a non-Error term means runtime
        # extension gap (typical for higher-order partial application).
        # Bare assertion-failed without HE-side error means runtime gap.
        if printf '%s\n' "$he_stdout" | grep -qE 'IncorrectNumberOfArguments|BadType|TypeMismatch'; then
            category=he_runtime_extension_gap
            reason='--he runtime rejects translator output (extension surface)'
            next_action='inspect src/he/he_translator.pl, src/he/he_natives.pl; produce minimal repro'
        elif [ "$he_rc" = 124 ]; then
            category=he_runtime_gap_core
            reason='--he timed out on translator output'
            next_action='inspect for translator-emitted nontermination; minimal repro'
        elif [ "$he_rc" = 0 ]; then
            # Exit 0 but assertion marker → assertion failed even though rc=0
            category=he_runtime_gap_core
            reason='--he ran but assertion fired'
            next_action='inspect translator output vs upstream HE; minimal repro'
        else
            category=he_runtime_gap_core
            reason="--he exit=$he_rc with stderr/stdout error"
            next_action='inspect translator output; minimal repro'
        fi
        # Save artefacts for later triage.
        printf '%s\n' "$he_stdout" > "$GAPS_DIR/${base}.he.stdout"
        printf '%s\n' "$he_stderr" > "$GAPS_DIR/${base}.he.stderr"
        cp -- "$generated" "$GAPS_DIR/${base}.translated.metta"
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$rel" "$category" "$rel_gen" "$default_rc" "$he_rc" "$reason" "$next_action" \
        >> "$INVENTORY"
    if [ "$category" = translated_passes ]; then
        # Compute ratio_wall safely (default_wall may be 0.00).
        local ratio
        if [ -n "$default_wall" ] && [ -n "$he_wall" ] && [ "$default_wall" != "NA" ] && [ "$he_wall" != "NA" ]; then
            ratio=$(awk -v a="$he_wall" -v b="$default_wall" 'BEGIN{ if (b+0 > 0) printf "%.3f", a/b; else printf "NA" }')
        else
            ratio=NA
        fi
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
            "$rel" "$rel_gen" "$default_wall" "$default_rss" \
            "$he_wall" "$he_rss" "$ratio" "$category" "-" \
            >> "$BENCH"
    fi
    printf '%s %s default(rc=%s w=%s r=%s) he(rc=%s w=%s r=%s)\n' \
        "$category" "$rel" "$default_rc" "$default_wall" "$default_rss" \
        "$he_rc" "$he_wall" "$he_rss" | tee -a "$LOG"
}

# ------------------------------------------------------------------
# Main loop
# ------------------------------------------------------------------

while IFS= read -r f; do
    classify_and_record "$f"
    processed=$((processed + 1))
    if [ "$LIMIT" -gt 0 ] && [ "$processed" -ge "$LIMIT" ]; then
        printf '\nstopping after --limit %s\n' "$LIMIT" | tee -a "$LOG"
        break
    fi
done < <(find "$ROOT/examples" -maxdepth 1 -type f -name '*.metta' | sort)

# ------------------------------------------------------------------
# Summary
# ------------------------------------------------------------------

count_cat() {
    awk -F'\t' -v c="$1" 'NR>1 && $2==c {n++} END{print n+0}' "$INVENTORY"
}

{
    printf '\n--- inventory summary ---\n'
    for c in translated_passes he_runtime_gap_core he_runtime_extension_gap \
             translator_gap_core petta_specific_no_translation \
             external_or_interactive already_he default_source_fails; do
        printf '  %s: %s\n' "$c" "$(count_cat "$c")"
    done
    printf '\nINVENTORY %s\n' "$INVENTORY"
    printf 'BENCH     %s\n' "$BENCH"
    printf 'GAPS      %s\n' "$GAPS_DIR"
    printf 'LOG       %s\n' "$LOG"
} | tee -a "$LOG"
