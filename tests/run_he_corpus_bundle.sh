#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "$0")" && pwd)
ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
TOOLS_DIR="$SCRIPT_DIR/tools"

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
LIMIT_KB=${LIMIT_KB:-6291456}
SWIPL_STACK_LIMIT=${SWIPL_STACK_LIMIT:-4g}
SWIPL_THREADS=${SWIPL_THREADS:-false}
HE_LOG_DIR=${HE_LOG_DIR:-"$ROOT/.he-logs"}
LOG=${LOG:-"$HE_LOG_DIR/petta_he_corpus_$(date -u +%Y%m%dT%H%M%SZ).log"}
FAILLOG=${FAILLOG:-"$HE_LOG_DIR/petta_he_corpus_failures_$(date -u +%Y%m%dT%H%M%SZ).log"}
log_base=$(basename -- "$LOG")
log_stamp=${log_base#petta_he_corpus_}
log_stamp=${log_stamp%.log}
HE_CORE_SEVERITY_SCRIPT=${HE_CORE_SEVERITY_SCRIPT:-"$TOOLS_DIR/generate_he_core_severity_tsv.sh"}
HE_CORE_SEVERITY_TSV=${HE_CORE_SEVERITY_TSV:-"$HE_LOG_DIR/he_core_severity_${log_stamp}.tsv"}
STRICT_HE_CORE=${STRICT_HE_CORE:-0}
STRICT_ALL=${STRICT_ALL:-0}

# The exit code assigned by `timeout` when its child wall-clock runs out.
# GNU coreutils uses 124. Keep a single source of truth so
# assert_fail/crashed/timed_out stay distinguishable.
readonly TIMEOUT_RC=124

collect_files() {
    find "$CORPUS_ROOT" -type f -name '*.metta' | sort
}

canonical_mirror_duplicates() {
    local cetta_dir=$CORPUS_ROOT/cetta_tests
    local canon_dir=$CORPUS_ROOT/hyperon_scripts
    [ -d "$cetta_dir" ] || return 0
    [ -d "$canon_dir" ] || return 0
    local file base canon
    while IFS= read -r file; do
        base=${file##*/}
        base=${base#he_}
        canon=$canon_dir/$base
        if [ -f "$canon" ] && cmp -s "$file" "$canon"; then
            printf '%s\n' "${file#$CORPUS_ROOT/}"
        fi
    done < <(find "$cetta_dir" -maxdepth 1 -type f -name 'he_*.metta' | sort)
}

mkdir -p "$(dirname -- "$LOG")" "$(dirname -- "$FAILLOG")" "$HE_ORACLE_HOME"
: > "$LOG"
: > "$FAILLOG"

mirror_dups=$(canonical_mirror_duplicates || true)
if [ -n "$mirror_dups" ]; then
    {
        printf 'ERROR: duplicate canonical HE mirror files are stored under cetta_tests.\n'
        printf 'Remove or prune these copies before running the HE corpus:\n'
        printf '%s\n' "$mirror_dups"
    } | tee -a "$LOG" >&2
    exit 2
fi

ulimit -v "$LIMIT_KB"
export SWIPL_STACK_LIMIT
export SWIPL_THREADS

total=0
skipped=0
skipped_fixture=0
skipped_admin=0
skipped_env=0
skipped_workload=0
skipped_nonpetta_extension=0
hyperon_seen=0
cetta_seen=0
hyperon_runnable=0
cetta_runnable=0
full_match=0
petta_supports_more=0
output_shape_differs=0
crashed=0
timed_out=0
assert_fail=0
no_oracle_clean=0
no_oracle_nonzero=0
declare -A cat_total=()
declare -A cat_same=()
declare -A cat_diff=()
categories=()
timed_out_files=()
crashed_files=()
assert_fail_files=()
upstream_only_files=()
oracle_quirk_files=()

# Detect a halt(1) from he_assert_same_results / he_assert_set_results.
# Anchored at start of line so it does not false-match on files that
# legitimately print the words "Assertion failed:" as program output.
is_assertion_failure_output() {
    printf '%s' "$1" | grep -q '^Assertion failed:\|\\nAssertion failed:'
}

# A runtime's output "effectively failed" when its result stream is an
# (Error ...) atom rather than a real answer. Upstream HE commonly exits
# rc=0 while printing [(Error (import! ...) Failed to resolve module ...)]
# for things PeTTa can load natively (str, fs, system, mork, relative
# imports, workload helpers). We treat those as upstream-couldn't-load,
# not as output-shape disagreements.
#
# Input is the already-normalized output (newlines escaped as the literal
# two-character sequence \n).
has_error_atom_output() {
    local out=$1
    # After normalize_output strips the outer [...] singleton wrap, a result
    # like [(Error ...)] becomes (Error ...). Match both shapes, at the start
    # and after any escaped newline boundary.
    case "$out" in
        '(Error'*)        return 0 ;;
        '[(Error'*)       return 0 ;;
        *'\n(Error'*)     return 0 ;;
        *'\n[(Error'*)    return 0 ;;
    esac
    return 1
}

{
    printf '# PeTTa --he Corpus Bundle\n\n'
    printf 'Corpus: `%s`\n' "$CORPUS_ROOT"
    printf 'PeTTa runner: `%s`\n' "$RUN_SH"
    if [ -n "$HE_METTA_BIN" ]; then
        printf 'Upstream HE oracle: `%s`\n' "$HE_METTA_BIN"
        printf 'Upstream HE HOME: `%s`\n' "$HE_ORACLE_HOME"
    else
        printf 'Upstream HE oracle: _not set (HE_METTA_BIN unset)_\n'
    fi
    printf '\n'
} | tee -a "$LOG" > /dev/null

while IFS= read -r file; do
    total=$((total + 1))
    rel=${file#"$CORPUS_ROOT"/}
    case "$rel" in
        hyperon_scripts/*) hyperon_seen=$((hyperon_seen + 1)) ;;
        cetta_tests/*) cetta_seen=$((cetta_seen + 1)) ;;
    esac
    if reason=$(he_corpus_skip_reason "$rel" "$file"); then
        skipped=$((skipped + 1))
        case "$reason" in
            cetta-admin) skipped_admin=$((skipped_admin + 1)) ;;
            he-no-python-env) skipped_env=$((skipped_env + 1)) ;;
            cetta-workload) skipped_workload=$((skipped_workload + 1)) ;;
            cetta-nonpetta-he-extension) skipped_nonpetta_extension=$((skipped_nonpetta_extension + 1)) ;;
            *) skipped_fixture=$((skipped_fixture + 1)) ;;
        esac
        printf 'SKIP [%s] %s\n' "$reason" "$rel" | tee -a "$LOG"
        continue
    fi
    case "$rel" in
        hyperon_scripts/*) hyperon_runnable=$((hyperon_runnable + 1)) ;;
        cetta_tests/*) cetta_runnable=$((cetta_runnable + 1)) ;;
    esac

    petta_pair=$(run_capture petta "$RUN_SH" --he "$file" --silent)
    petta_rc=${petta_pair%%$'\t'*}
    petta_out=${petta_pair#*$'\t'}

    # Classify PeTTa-side health first. These take precedence over any
    # upstream comparison because they describe whether PeTTa itself
    # completed the file, not whether PeTTa agreed with upstream.
    petta_label=''
    case "$petta_rc" in
        "$TIMEOUT_RC")
            timed_out=$((timed_out + 1))
            timed_out_files+=("$rel")
            petta_label='TIMED_OUT'
            ;;
        1)
            if is_assertion_failure_output "$petta_out"; then
                assert_fail=$((assert_fail + 1))
                assert_fail_files+=("$rel")
                petta_label='ASSERT_FAIL'
            fi
            ;;
        0) ;;  # healthy; classified below against the oracle (if any).
        *)
            crashed=$((crashed + 1))
            crashed_files+=("$rel")
            petta_label='CRASHED'
            ;;
    esac

    if [ -n "$petta_label" ]; then
        printf '%s %s\n' "$petta_label" "$rel" | tee -a "$LOG"
        if [ "$petta_label" = CRASHED ] || [ "$petta_label" = TIMED_OUT ]; then
            {
                printf '%s %s exit=%s\n' "$petta_label" "$rel" "$petta_rc"
                printf '%s\n' "$petta_out" | tail -40
            } | tee -a "$FAILLOG" > /dev/null
        fi
        continue
    fi

    # PeTTa side is healthy (petta_rc == 0, or petta_rc == 1 without an
    # assertion-failure prefix — rare; fold into crashed below if we see it).
    if [ "$petta_rc" != 0 ]; then
        crashed=$((crashed + 1))
        crashed_files+=("$rel")
        printf 'CRASHED %s\n' "$rel" | tee -a "$LOG"
        continue
    fi

    # No oracle configured: we can say PeTTa ran cleanly but nothing about
    # agreement. Keep this row in the no_oracle bucket so the summary math
    # remains honest.
    if [ -z "$HE_METTA_BIN" ]; then
        no_oracle_clean=$((no_oracle_clean + 1))
        printf 'NO_ORACLE_CLEAN %s\n' "$rel" | tee -a "$LOG"
        continue
    fi

    # Oracle available: run upstream HE and compare.
    he_pair=$(run_capture he "$HE_METTA_BIN" "$file")
    he_rc=${he_pair%%$'\t'*}
    he_out=${he_pair#*$'\t'}

    # Classification of the upstream-vs-PeTTa pairing:
    #   1. Upstream exited nonzero OR emitted an (Error ...) result atom
    #      → PETTA_SUPPORTS_MORE (as long as PeTTa did not also emit an
    #        error atom). This covers both hard-failing upstream (rc != 0)
    #        and soft-failing upstream (rc == 0 with error-atom output).
    #   2. Upstream produced a real answer AND PeTTa produced an error
    #      atom → either UPSTREAM_ONLY (true regression) or
    #      UPSTREAM_QUIRK (known oracle oddity where PeTTa keeps the
    #      spec-shaped surface).
    #   3. Outputs identical → FULL_MATCH.
    #   4. Both produced real outputs that disagree → EXTENSION_OUTPUT_SHAPE.
    he_errored=0
    if [ "$he_rc" != 0 ] || has_error_atom_output "$he_out"; then
        he_errored=1
    fi
    petta_errored=0
    if has_error_atom_output "$petta_out"; then
        petta_errored=1
    fi

    if [ "$he_errored" = 1 ] && [ "$petta_errored" = 0 ]; then
        petta_supports_more=$((petta_supports_more + 1))
        label='PETTA_SUPPORTS_MORE'
    elif [ "$he_errored" = 0 ] && [ "$petta_errored" = 1 ]; then
        output_shape_differs=$((output_shape_differs + 1))
        kind=$(upstream_only_kind "$rel")
        case "$kind" in
            oracle-quirk)
                oracle_quirk_files+=("$rel")
                label='UPSTREAM_QUIRK'
                ;;
            *)
                upstream_only_files+=("$rel")
                label='UPSTREAM_ONLY'
                ;;
        esac
        class_pair=$(classify_case "$rel" diff "$he_out" "$petta_out")
        category=${class_pair%%$'\t'*}
        remember_category "$category" diff
    elif [ "$he_out" = "$petta_out" ]; then
        full_match=$((full_match + 1))
        label='FULL_MATCH'
        class_pair=$(classify_case "$rel" same "$he_out" "$petta_out")
        category=${class_pair%%$'\t'*}
        remember_category "$category" same
    else
        output_shape_differs=$((output_shape_differs + 1))
        label='EXTENSION_OUTPUT_SHAPE'
        class_pair=$(classify_case "$rel" diff "$he_out" "$petta_out")
        category=${class_pair%%$'\t'*}
        remember_category "$category" diff
    fi

    # Annotate the log with the classification category for extension rows
    # so triage does not need to re-run classify_case after the fact.
    if [ "$label" = EXTENSION_OUTPUT_SHAPE ]; then
        printf '%s [%s] %s\n' "$label" "$category" "$rel" | tee -a "$LOG"
    else
        printf '%s %s\n' "$label" "$rel" | tee -a "$LOG"
    fi
done < <(collect_files)

he_core_total=${cat_total[he-core]:-0}
he_core_match=${cat_same[he-core]:-0}
he_core_diff=${cat_diff[he-core]:-0}
shape_diff_type=${cat_diff[type-behavior]:-0}
shape_diff_state=${cat_diff[state-surface]:-0}
shape_diff_doc=${cat_diff[doc-surface]:-0}
shape_diff_presentation=${cat_diff[presentation]:-0}
shape_diff_core_raw=${cat_diff[he-core]:-0}
shape_diff_format=${cat_diff[format-only]:-0}
shape_diff_helper=${cat_diff[extension-helper-surface]:-0}
shape_diff_support_more=${cat_diff[support-more]:-0}
shape_diff_callable_gap=${cat_diff[callable-head-gap]:-0}
shape_diff_extension=${cat_diff[extension]:-0}
shape_diff_workload=${cat_diff[workload]:-0}
shape_diff_support=${cat_diff[support-probe]:-0}
shape_diff_import=${cat_diff[import-compat]:-0}
oracle_quirk_count=${#oracle_quirk_files[@]}
shape_diff_core=$((shape_diff_core_raw - oracle_quirk_count))
if [ "$shape_diff_core" -lt 0 ]; then
    shape_diff_core=0
fi

petta_ran_clean=$((full_match + petta_supports_more + output_shape_differs + no_oracle_clean))
exact_other=$((full_match - he_core_match))

{
    printf '\n'
    printf 'PeTTa --he — %s HE test files (%s).\n' "$total" "$CORPUS_ROOT"
    printf '  · hyperon-experimental rows seen/runnable: %s/%s\n' "$hyperon_runnable" "$hyperon_seen"
    printf '  · CeTTa rows seen/runnable: %s/%s\n' "$cetta_runnable" "$cetta_seen"
    printf '\n'
    if [ -n "$HE_METTA_BIN" ]; then
        printf 'HE-spec-core conformance: %s/%s files match upstream HE exactly.\n' \
            "$he_core_match" "$he_core_total"
        printf '\n'
        printf 'PeTTa completed %s files cleanly.\n' "$petta_ran_clean"
        printf '  · %s files: exact match to upstream HE inside the HE-spec core.\n' "$he_core_match"
        if [ "$exact_other" -gt 0 ]; then
            printf '  · %s more files: exact match to upstream HE outside the HE-spec core.\n' "$exact_other"
        fi
        printf '  · %s files: PeTTa supports features upstream HE cannot load\n' "$petta_supports_more"
        printf '              (extensions, CeTTa-added imports, workload helpers).\n'
        if [ "$output_shape_differs" -gt 0 ]; then
            printf '\n'
            printf 'Non-exact observations where both engines ran: %s files.\n' "$output_shape_differs"
            [ "$shape_diff_presentation" -gt 0 ] && \
                printf '  · %s files: presentation-only output shape (alpha-renaming / trailing empty bags).\n' "$shape_diff_presentation"
            [ "$shape_diff_format" -gt 0 ] && \
                printf '  · %s files: pretty-output formatting only.\n' "$shape_diff_format"
            [ "$shape_diff_helper" -gt 0 ] && \
                printf '  · %s files: CeTTa/PeTTa extension helpers — PeTTa evaluates or commits\n     more directly where upstream leaves raw helper forms.\n' "$shape_diff_helper"
            [ "$shape_diff_support_more" -gt 0 ] && \
                printf '  · %s files: support wins — PeTTa finds answers upstream leaves empty.\n' "$shape_diff_support_more"
            [ "$shape_diff_callable_gap" -gt 0 ] && \
                printf '  · %s files: callable-head gap (currently the py-atom probe).\n' "$shape_diff_callable_gap"
            [ "$oracle_quirk_count" -gt 0 ] && \
                printf '  · %s files: upstream-oracle quirk(s) — PeTTa keeps the spec-shaped result\n     where upstream currently leaks an odd surface.\n' "$oracle_quirk_count"
            [ "$shape_diff_core" -gt 0 ] && \
                printf '  · %s files: HE-core semantic disagreement(s) — investigate immediately.\n' "$shape_diff_core"
            [ "$shape_diff_type" -gt 0 ] && \
                printf '  · %s files: type-behavior observations.\n' "$shape_diff_type"
            [ "$shape_diff_state" -gt 0 ] && \
                printf '  · %s files: state/unit-result output-shape observations.\n' "$shape_diff_state"
            [ "$shape_diff_doc" -gt 0 ] && \
                printf '  · %s files: doc-surface observations.\n' "$shape_diff_doc"
            [ "$shape_diff_import" -gt 0 ] && \
                printf '  · %s files: import-compat observations.\n' "$shape_diff_import"
            [ "$shape_diff_extension" -gt 0 ] && \
                printf '  · %s files: extension-lane observations.\n' "$shape_diff_extension"
            [ "$shape_diff_workload" -gt 0 ] && \
                printf '  · %s files: workload-lane observations.\n' "$shape_diff_workload"
            [ "$shape_diff_support" -gt 0 ] && \
                printf '  · %s files: support/probe observations.\n' "$shape_diff_support"
        fi
    else
        printf '(No upstream HE oracle configured; HE_METTA_BIN is unset.)\n'
        printf '\n'
        printf 'PeTTa completed %s files cleanly.\n' "$no_oracle_clean"
    fi

    if [ "${#upstream_only_files[@]}" -gt 0 ]; then
        printf '\n'
        printf 'PeTTa regressions (upstream HE handled it; PeTTa returned an error atom):\n'
        for f in "${upstream_only_files[@]}"; do
            printf '  · %s\n' "$f"
        done
    fi
    if [ "${#oracle_quirk_files[@]}" -gt 0 ]; then
        printf '\n'
        printf 'Oracle quirks (upstream differs; PeTTa keeps the spec-shaped surface):\n'
        for f in "${oracle_quirk_files[@]}"; do
            printf '  · %s\n' "$f"
        done
    fi

    printf '\n'
    printf 'Problems:\n'
    if [ "$timed_out" -gt 0 ]; then
        printf '  · %s timed out:\n' "$timed_out"
        for f in "${timed_out_files[@]}"; do
            printf '      %s\n' "$f"
        done
        printf '    (To isolate whether --he is responsible, rerun the file under\n'
        printf '     default PeTTa: %s <file> --silent.)\n' "$RUN_SH"
    else
        printf '  · 0 timed out.\n'
    fi
    if [ "$crashed" -gt 0 ]; then
        printf '  · %s crashed:\n' "$crashed"
        for f in "${crashed_files[@]}"; do
            printf '      %s\n' "$f"
        done
    else
        printf '  · 0 crashed.\n'
    fi
    if [ "$assert_fail" -gt 0 ]; then
        printf '  · %s assertion failures:\n' "$assert_fail"
        for f in "${assert_fail_files[@]}"; do
            printf '      %s\n' "$f"
        done
    else
        printf '  · 0 assertion failures.\n'
    fi
    if [ "$no_oracle_nonzero" -gt 0 ]; then
        printf '  · %s non-oracle nonzero exits (no upstream to compare).\n' "$no_oracle_nonzero"
    fi
    printf '\n'
    printf '%s files skipped.\n' "$skipped"
    if [ "$skipped_fixture" -gt 0 ]; then
        printf '  · %s malformed/obsolete fixture(s), not runnable standalone.\n' "$skipped_fixture"
    fi
    if [ "$skipped_admin" -gt 0 ]; then
        printf '  · %s CeTTa administrative/profile-inventory probe(s), kept out of PeTTa --he conformance.\n' "$skipped_admin"
    fi
    if [ "$skipped_env" -gt 0 ]; then
        printf '  · %s environment-specific file(s) that require Python-enabled module layout.\n' "$skipped_env"
    fi
    if [ "$skipped_workload" -gt 0 ]; then
        printf '  · %s CeTTa benchmark/workload file(s), kept out of the correctness lane.\n' "$skipped_workload"
    fi
    if [ "$skipped_nonpetta_extension" -gt 0 ]; then
        printf '  · %s CeTTa file(s) using non-PeTTa HE-extension surfaces.\n' "$skipped_nonpetta_extension"
    fi
    printf '\n'
    printf 'LOG %s\n' "$LOG"
    printf 'FAILLOG %s\n' "$FAILLOG"
} | tee -a "$LOG"

if [ -x "$HE_CORE_SEVERITY_SCRIPT" ]; then
    "$HE_CORE_SEVERITY_SCRIPT" "$LOG" "$HE_CORE_SEVERITY_TSV"
    printf 'SEVERITY_TSV %s\n' "$HE_CORE_SEVERITY_TSV" | tee -a "$LOG"
fi

# Exit-code gating.
#   - Default: exit nonzero only for PeTTa-side health problems (crashed,
#     timed_out, assert_fail). Extension output-shape observations and PeTTa-supports-more
#     are classified and not fail conditions.
#   - STRICT_HE_CORE=1: also fail if any HE-spec-core file had an
#     output-shape observation (0 today; this is the conformance gate).
#   - STRICT_ALL=1: also fail on any extension output-shape observation.
rc=0
if [ "$crashed" -gt 0 ] || [ "$timed_out" -gt 0 ] || [ "$assert_fail" -gt 0 ]; then
    rc=1
fi
if [ "$STRICT_HE_CORE" = 1 ] && [ "$he_core_diff" -gt 0 ]; then
    rc=1
fi
if [ "$STRICT_ALL" = 1 ] && [ "$output_shape_differs" -gt 0 ]; then
    rc=1
fi
exit "$rc"
