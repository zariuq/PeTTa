#!/usr/bin/env bash
# Translator-first PeTTa→HE examples survey + benchmark.
#
# For each examples/*.metta (maxdepth 1):
#   1. Run default PeTTa, capture wall/rss/exit.
#   2. If translation-eligible: run translator, run --he, capture
#      wall/rss/exit.
#   3. Classify the row using the vocabulary from the brief at
#      tmp/hepetta_examples_translation_bench_instructions_20260425.md
#      (translated_passes, correct_but_perf_gap, translator_gap_*,
#       he_runtime_gap_*, portable_extension_lowered,
#      petta_specific_no_translation, external_or_interactive,
#      already_he, default_source_fails).
#
# Outputs:
#   .he-logs/he_translation_inventory.tsv
#   .he-logs/he_translation_bench.tsv
#   .he-logs/he_translation_gaps/<base>.{he-stderr,he-stdout,translated}
#
# Translator commands recorded per-row so every generated portable output is
# reproducible.
# Ordinary portable outputs use:
#   examples/he_translated/*_he.metta
# Hyperpose-using sources also get an explicit portability split:
#   examples/he_translated/*_he_sequential.metta
#   examples/he_translated/*_he_parallel.metta

set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
RUN_SH=${RUN_SH:-"$ROOT/run.sh"}
TRANSLATE_SH=${TRANSLATE_SH:-/home/zar/claude/hyperon/translators/translate.sh}
LABEL_HE_EXAMPLES_SH=${LABEL_HE_EXAMPLES_SH:-"$ROOT/tests/tools/label_petta_he_examples.sh"}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-120}
WITNESS_TIMEOUT_SECONDS=${WITNESS_TIMEOUT_SECONDS:-20}
LIMIT_KB=${LIMIT_KB:-10485760}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
GENERATED_DIR=${GENERATED_DIR:-"$ROOT/examples/he_translated"}
INVENTORY=${INVENTORY:-"$HE_LOG_DIR/he_translation_inventory.tsv"}
BENCH=${BENCH:-"$HE_LOG_DIR/he_translation_bench.tsv"}
GAPS_DIR=${GAPS_DIR:-"$HE_LOG_DIR/he_translation_gaps"}
STAMP=${STAMP:-$(date -u +%Y%m%dT%H%M%SZ)_$$}
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
    printf 'source\tportable_category\tportable_translated\tdefault_exit\tportable_he_exit\tportable_reason\tportable_next_action\tparallel_category\tparallel_translated\tparallel_he_exit\tparallel_reason\tparallel_next_action\n' > "$INVENTORY"
    printf 'source\tportable_translated\tparallel_translated\tdefault_wall\tdefault_rss\tportable_wall\tportable_rss\tparallel_wall\tparallel_rss\tportable_ratio_wall\tparallel_ratio_wall\tportable_category\tparallel_category\tnotes\n' > "$BENCH"
    declare -A RESUME_DONE=()
fi

# ------------------------------------------------------------------
# Skip lists
# ------------------------------------------------------------------

# Already_he: filename-prefix he_*.metta is excluded by glob below.
EXTERNAL_OR_INTERACTIVE='greedy_chess.metta repl.metta llm_cities.metta torch.metta git_import.metta git_import2.metta python.metta python_import.metta'

PETTA_SPECIFIC='translatorrule.metta translatorrule_fib.metta translatorrule_for.metta translatepredicate.metta streamops.metta metta4_streams.metta mutex_and_transaction.metta state.metta nilbc.metta prologimport.metta myinterpreter.metta selfprog.metta smartdispatch.metta builin_types.metta parametric_types.metta recursive_types.metta meta_types.metta types_dependent.metta types_nondet.metta mettaset.metta spaces.metta spaces_find.metta spaces_removeallatoms.metta spaces_succeedspredicate.metta'

# Whether a given basename is in a space-separated list.
in_list() {
    local needle=$1; shift
    local hay=$1
    case " $hay " in
        *" $needle "*) return 0 ;;
        *)             return 1 ;;
    esac
}

translation_witness_for_source() {
    case "$1" in
        examples/tilepuzzle.metta)
            printf '%s\n' 'tests/profile_repros/he_tilepuzzle_bfs_500_witness.metta'
            ;;
        examples/peano.metta)
            printf '%s\n' 'tests/profile_repros/he_peano_demo_50_witness.metta'
            ;;
        examples/hyperpose_primes.metta)
            printf '%s\n' 'tests/profile_repros/he_hyperpose_primes_once_witness.metta'
            ;;
        examples/holbenchmark.metta)
            printf '%s\n' 'tests/profile_repros/he_holbenchmark_witness.metta'
            ;;
        examples/matespace.metta)
            printf '%s\n' 'tests/profile_repros/he_matespace_demo_4_witness.metta'
            ;;
        examples/matespace2.metta)
            printf '%s\n' 'tests/profile_repros/he_matespace2_demo_4_witness.metta'
            ;;
        examples/matespacefast.metta)
            printf '%s\n' 'tests/profile_repros/he_matespacefast_demo_6_witness.metta'
            ;;
        examples/nars_tuffy.metta)
            printf '%s\n' 'tests/profile_repros/he_nars_tuffy_smallkb_witness.metta'
            ;;
        *)
            return 1
            ;;
    esac
}

source_uses_hyperpose() {
    grep -Eq '(^|[^[:alnum:]_-])hyperpose([^[:alnum:]_-]|$)' "$ROOT/$1"
}

explicit_parallel_lane_for_source() {
    local rel=$1
    # Keep this intentionally narrow: only sources whose main semantic
    # portability issue is deparallelized hyperpose currently earn a second
    # translated lane. Other PeTTa-only surfaces stay in the normal skip
    # buckets until we have a similarly crisp portability contract.
    if source_uses_hyperpose "$rel"; then
        printf '%s\n' 'hyperpose'
    fi
}

portable_generated_for_source() {
    local rel=$1
    local base=$2
    if source_uses_hyperpose "$rel"; then
        printf '%s\n' "$GENERATED_DIR/${base}_he_sequential.metta"
    else
        printf '%s\n' "$GENERATED_DIR/${base}_he.metta"
    fi
}

# ------------------------------------------------------------------
# Capture helpers
# ------------------------------------------------------------------

# Captures: wall (s, %e), max RSS (KB, %M), exit (%x).
# stdout is captured separately for assertion/error inspection.
run_capture_timeout() {
    local timeout_seconds=$1
    local label=$2
    shift 2
    local err
    err=$(mktemp)
    local out
    set +e
    out=$(/usr/bin/time -f '__TIME__ wall=%e rss_kb=%M exit=%x' \
            timeout --kill-after=5 "$timeout_seconds" "$@" 2>"$err")
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
    if [ "$cmd_rc" != 0 ]; then
        exit_field=$cmd_rc
    fi
    # Returns: rc<TAB>wall<TAB>rss<TAB>stdout<\037>stderr  (\037 separates)
    # We use \037 (US) since output may contain newlines/tabs.
    printf '%s\t%s\t%s\t%s\037%s' \
        "$exit_field" "$wall" "$rss" "$out" "$stderr_clean"
}

run_capture() {
    run_capture_timeout "$TIMEOUT_SECONDS" "$@"
}

# Detect assertion failures the same way smoke does.
has_assert_failure() {
    printf '%s\n' "$1" | grep -qE '❌|Assertion failed:|IncorrectNumberOfArguments|BadType|TypeMismatch'
}

is_timeout_rc() {
    case "$1" in
        124|137|143) return 0 ;;
        *) return 1 ;;
    esac
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
    local generated
    generated=$(portable_generated_for_source "$rel" "$base")
    local generated_parallel="$GENERATED_DIR/${base}_he_parallel.metta"
    local witness_rel witness_path

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
        printf '%s\talready_he\t-\t-\t-\tHE-style example; covered by run_he_profile_suite.sh\t-\t-\t-\t-\t-\t-\n' \
            "$rel" >> "$INVENTORY"
        printf 'SKIP[already_he] %s\n' "$rel" | tee -a "$LOG"
        return
    esac

    # Bucket 2 — external_or_interactive (skip)
    if in_list "$fname" "$EXTERNAL_OR_INTERACTIVE"; then
        printf '%s\texternal_or_interactive\t-\t-\t-\tnetwork/LLM/PyTorch/REPL/UI/Python bridge\t-\t-\t-\t-\t-\t-\n' \
            "$rel" >> "$INVENTORY"
        printf 'SKIP[external_or_interactive] %s\n' "$rel" | tee -a "$LOG"
        return
    fi

    # Bucket 3 — petta_specific (skip translation, classify)
    if in_list "$fname" "$PETTA_SPECIFIC"; then
        printf '%s\tpetta_specific_no_translation\t-\t-\t-\tdeliberately PeTTa-only construct\t-\t-\t-\t-\t-\t-\n' \
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
        printf '%s\tdefault_source_fails\t-\t%s\t-\toriginal PeTTa run failed (rc=%s)\tinvestigate before claiming HE compat\t-\t-\t-\t-\t-\n' \
            "$rel" "$default_rc" "$default_rc" >> "$INVENTORY"
        printf 'SKIP[default_source_fails] %s rc=%s\n' "$rel" "$default_rc" | tee -a "$LOG"
        return
    fi

    # ----- Translate -----
    local trans_log="$GAPS_DIR/${base}.translate.stderr"
    if ! "$TRANSLATE_SH" petta2he "$source" "$generated" >"$GAPS_DIR/${base}.translate.stdout" 2>"$trans_log"; then
        printf '%s\ttranslator_gap_core\t-\t%s\t-\ttranslator command failed; see %s\tflag for petta_to_he.pl\t-\t-\t-\t-\t-\n' \
            "$rel" "$default_rc" "$trans_log" >> "$INVENTORY"
        printf 'GAP[translator_failed] %s\n' "$rel" | tee -a "$LOG"
        return
    fi
    "$LABEL_HE_EXAMPLES_SH" --file "$generated" "$source"
    rm -f "$GAPS_DIR/${base}.translate.stdout" "$trans_log"

    local rel_gen=${generated#"$ROOT"/}
    local rel_gen_parallel=-
    witness_rel=$(translation_witness_for_source "$rel" || true)
    witness_path=
    if [ -n "$witness_rel" ]; then
        witness_path="$ROOT/$witness_rel"
        if [ ! -f "$witness_path" ]; then
            printf 'missing witness for %s: %s\n' "$rel" "$witness_path" >&2
            exit 1
        fi
    fi

    local witness_pkt witness_rc witness_wall witness_rss witness_stdout witness_stderr
    local witness_passed=0
    local parallel_lane_kind=
    parallel_lane_kind=$(explicit_parallel_lane_for_source "$rel" || true)
    if [ -n "$witness_path" ]; then
        witness_pkt=$(run_capture_timeout "$WITNESS_TIMEOUT_SECONDS" he-witness "$RUN_SH" --he "$witness_path" --silent)
        witness_rc=${witness_pkt%%$'\t'*}
        rest1=${witness_pkt#*$'\t'}
        witness_wall=${rest1%%$'\t'*}
        rest2=${rest1#*$'\t'}
        witness_rss=${rest2%%$'\t'*}
        rest3=${rest2#*$'\t'}
        witness_stdout=${rest3%%$'\037'*}
        witness_stderr=${rest3#*$'\037'}
        if [ "$witness_rc" = 0 ] && ! has_assert_failure "$witness_stdout" && ! has_assert_failure "$witness_stderr"; then
            witness_passed=1
        else
            printf '%s\n' "$witness_stdout" > "$GAPS_DIR/${base}.witness.he.stdout"
            printf '%s\n' "$witness_stderr" > "$GAPS_DIR/${base}.witness.he.stderr"
        fi
    fi

    # ----- Run --he on portable translated output -----
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

    # ----- Classify portable lane -----
    local portable_category portable_reason portable_next_action
    local portable_extension_lowered=0
    if [ "$he_rc" = 0 ] && ! has_assert_failure "$he_stdout" && ! has_assert_failure "$he_stderr"; then
        portable_category=translated_passes
        portable_reason='portable translator output runs cleanly under --he'
        portable_next_action='-'
    else
        if [ "$parallel_lane_kind" = hyperpose ]; then
            portable_category=he_runtime_extension_gap
            portable_reason='source uses hyperpose; portable translation lowered it to sequential superpose and that workload still fails under --he'
            portable_next_action='compare against _he_parallel or direct PeTTa --he hyperpose behavior on a reduced repro'
            portable_extension_lowered=1
        elif is_timeout_rc "$he_rc" && [ "$witness_passed" = 1 ]; then
            portable_category=correct_but_perf_gap
            portable_reason="portable full translated run timed out, but reduced witness $witness_rel passes under --he"
            portable_next_action='keep full portable translation; treat as performance/capacity gap; profile the full workload'
        elif printf '%s\n' "$he_stdout" | grep -qE 'IncorrectNumberOfArguments|BadType|TypeMismatch'; then
            portable_category=he_runtime_extension_gap
            portable_reason='--he runtime rejects portable translator output (extension surface)'
            portable_next_action='inspect src/he/he_translator.pl, src/he/he_natives.pl; produce minimal repro'
        elif is_timeout_rc "$he_rc"; then
            portable_category=he_runtime_gap_core
            portable_reason='--he timed out on portable translator output'
            portable_next_action='inspect for translator-emitted nontermination; minimal repro'
        elif [ "$he_rc" = 0 ]; then
            portable_category=he_runtime_gap_core
            portable_reason='--he ran portable translator output but assertion fired'
            portable_next_action='inspect translator output vs upstream HE; minimal repro'
        else
            portable_category=he_runtime_gap_core
            portable_reason="--he exit=$he_rc with stderr/stdout error on portable translator output"
            portable_next_action='inspect translator output; minimal repro'
        fi
        printf '%s\n' "$he_stdout" > "$GAPS_DIR/${base}.he.stdout"
        printf '%s\n' "$he_stderr" > "$GAPS_DIR/${base}.he.stderr"
        cp -- "$generated" "$GAPS_DIR/${base}.translated.metta"
    fi

    # ----- Optional HE++ parallel lane for hyperpose sources -----
    local parallel_category=- parallel_reason=- parallel_next_action=-
    local parallel_he_rc=- parallel_he_wall=NA parallel_he_rss=NA
    local parallel_stdout= parallel_stderr=
    if [ "$parallel_lane_kind" = hyperpose ]; then
        local trans_parallel_log="$GAPS_DIR/${base}.translate_parallel.stderr"
        if ! "$TRANSLATE_SH" petta2he --preserve-hyperpose "$source" "$generated_parallel" >"$GAPS_DIR/${base}.translate_parallel.stdout" 2>"$trans_parallel_log"; then
            parallel_category=translator_gap_core
            parallel_reason="parallel translator command failed; see $trans_parallel_log"
            parallel_next_action='inspect petta_to_he.pl hyperpose-preserving mode'
        else
            "$LABEL_HE_EXAMPLES_SH" --file "$generated_parallel" "$source"
            rm -f "$GAPS_DIR/${base}.translate_parallel.stdout" "$trans_parallel_log"
            rel_gen_parallel=${generated_parallel#"$ROOT"/}

            local parallel_pkt
            parallel_pkt=$(run_capture he-parallel "$RUN_SH" --he "$generated_parallel" --silent)
            parallel_he_rc=${parallel_pkt%%$'\t'*}
            rest1=${parallel_pkt#*$'\t'}
            parallel_he_wall=${rest1%%$'\t'*}
            rest2=${rest1#*$'\t'}
            parallel_he_rss=${rest2%%$'\t'*}
            rest3=${rest2#*$'\t'}
            parallel_stdout=${rest3%%$'\037'*}
            parallel_stderr=${rest3#*$'\037'}

            if [ "$parallel_he_rc" = 0 ] && ! has_assert_failure "$parallel_stdout" && ! has_assert_failure "$parallel_stderr"; then
                parallel_category=translated_passes
                parallel_reason='preserve-hyperpose translator output runs cleanly under --he'
                parallel_next_action='-'
            elif is_timeout_rc "$parallel_he_rc" && [ "$witness_passed" = 1 ]; then
                parallel_category=correct_but_perf_gap
                parallel_reason="parallel full translated run timed out, but reduced witness $witness_rel passes under --he"
                parallel_next_action='keep _he_parallel translation; treat as performance/capacity gap; profile the full workload'
            elif printf '%s\n' "$parallel_stdout" | grep -qE 'IncorrectNumberOfArguments|BadType|TypeMismatch'; then
                parallel_category=he_runtime_extension_gap
                parallel_reason='--he runtime rejects preserve-hyperpose translator output (HE++ extension surface)'
                parallel_next_action='inspect direct hyperpose runtime path and translated HE++ repro'
            elif is_timeout_rc "$parallel_he_rc"; then
                parallel_category=he_runtime_extension_gap
                parallel_reason='--he timed out on preserve-hyperpose translator output'
                parallel_next_action='profile translated _he_parallel workload and direct hyperpose runtime path'
            elif [ "$parallel_he_rc" = 0 ]; then
                parallel_category=he_runtime_extension_gap
                parallel_reason='--he ran preserve-hyperpose translator output but assertion fired'
                parallel_next_action='inspect translated _he_parallel output vs direct PeTTa --he behavior'
            else
                parallel_category=he_runtime_extension_gap
                parallel_reason="--he exit=$parallel_he_rc with stderr/stdout error on preserve-hyperpose translator output"
                parallel_next_action='inspect translated _he_parallel output'
            fi

            if [ "$parallel_category" != translated_passes ]; then
                printf '%s\n' "$parallel_stdout" > "$GAPS_DIR/${base}.he_parallel.stdout"
                printf '%s\n' "$parallel_stderr" > "$GAPS_DIR/${base}.he_parallel.stderr"
                cp -- "$generated_parallel" "$GAPS_DIR/${base}.translated_parallel.metta"
            fi
        fi
    fi

    if [ "$portable_extension_lowered" = 1 ]; then
        case "$parallel_category" in
            translated_passes|correct_but_perf_gap)
                portable_category=portable_extension_lowered
                portable_reason='portable _he_sequential translation intentionally sequentializes hyperpose; preserved-hyperpose lane carries the semantic compatibility claim'
                portable_next_action='-'
                ;;
        esac
    fi

    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
        "$rel" "$portable_category" "$rel_gen" "$default_rc" "$he_rc" "$portable_reason" "$portable_next_action" \
        "$parallel_category" "$rel_gen_parallel" "$parallel_he_rc" "$parallel_reason" "$parallel_next_action" \
        >> "$INVENTORY"

    local portable_ratio parallel_ratio
    if [ "$default_wall" != "NA" ] && [ "$he_wall" != "NA" ]; then
        portable_ratio=$(awk -v a="$he_wall" -v b="$default_wall" 'BEGIN{ if (b+0 > 0) printf "%.3f", a/b; else printf "NA" }')
    else
        portable_ratio=NA
    fi
    if [ "$default_wall" != "NA" ] && [ "$parallel_he_wall" != "NA" ]; then
        parallel_ratio=$(awk -v a="$parallel_he_wall" -v b="$default_wall" 'BEGIN{ if (b+0 > 0) printf "%.3f", a/b; else printf "NA" }')
    else
        parallel_ratio=NA
    fi
    if [ "$portable_category" = translated_passes ] || [ "$portable_category" = correct_but_perf_gap ] || \
       [ "$parallel_category" = translated_passes ] || [ "$parallel_category" = correct_but_perf_gap ]; then
        printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
            "$rel" "$rel_gen" "$rel_gen_parallel" "$default_wall" "$default_rss" \
            "$he_wall" "$he_rss" "$parallel_he_wall" "$parallel_he_rss" \
            "$portable_ratio" "$parallel_ratio" "$portable_category" "$parallel_category" "-" \
            >> "$BENCH"
    fi
    if [ -n "$witness_path" ]; then
        printf 'portable[%s] parallel[%s] %s default(rc=%s w=%s r=%s) witness(rc=%s w=%s r=%s) portable(rc=%s w=%s r=%s) parallel(rc=%s w=%s r=%s)\n' \
            "$portable_category" "$parallel_category" "$rel" \
            "$default_rc" "$default_wall" "$default_rss" \
            "$witness_rc" "$witness_wall" "$witness_rss" \
            "$he_rc" "$he_wall" "$he_rss" \
            "$parallel_he_rc" "$parallel_he_wall" "$parallel_he_rss" | tee -a "$LOG"
    else
        printf 'portable[%s] parallel[%s] %s default(rc=%s w=%s r=%s) portable(rc=%s w=%s r=%s) parallel(rc=%s w=%s r=%s)\n' \
            "$portable_category" "$parallel_category" "$rel" \
            "$default_rc" "$default_wall" "$default_rss" \
            "$he_rc" "$he_wall" "$he_rss" \
            "$parallel_he_rc" "$parallel_he_wall" "$parallel_he_rss" | tee -a "$LOG"
    fi
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

count_cat_col() {
    awk -F'\t' -v c="$1" -v col="$2" 'NR>1 && $col==c {n++} END{print n+0}' "$INVENTORY"
}

{
    printf '\n--- inventory summary ---\n'
    printf '  portable_translated_passes: %s\n' "$(count_cat_col translated_passes 2)"
    printf '  portable_correct_but_perf_gap: %s\n' "$(count_cat_col correct_but_perf_gap 2)"
    printf '  portable_extension_lowered: %s\n' "$(count_cat_col portable_extension_lowered 2)"
    printf '  portable_he_runtime_gap_core: %s\n' "$(count_cat_col he_runtime_gap_core 2)"
    printf '  portable_he_runtime_extension_gap: %s\n' "$(count_cat_col he_runtime_extension_gap 2)"
    printf '  portable_translator_gap_core: %s\n' "$(count_cat_col translator_gap_core 2)"
    printf '  portable_petta_specific_no_translation: %s\n' "$(count_cat_col petta_specific_no_translation 2)"
    printf '  portable_external_or_interactive: %s\n' "$(count_cat_col external_or_interactive 2)"
    printf '  portable_already_he: %s\n' "$(count_cat_col already_he 2)"
    printf '  portable_default_source_fails: %s\n' "$(count_cat_col default_source_fails 2)"
    printf '\n'
    for c in translated_passes correct_but_perf_gap \
             he_runtime_extension_gap translator_gap_core; do
        printf '  parallel_%s: %s\n' "$c" "$(count_cat_col "$c" 8)"
    done
    printf '\nINVENTORY %s\n' "$INVENTORY"
    printf 'BENCH     %s\n' "$BENCH"
    printf 'GAPS      %s\n' "$GAPS_DIR"
    printf 'LOG       %s\n' "$LOG"
} | tee -a "$LOG"
