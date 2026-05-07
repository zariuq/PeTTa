#!/usr/bin/env bash
set -euo pipefail

LOG=${1:?usage: generate_he_core_severity_tsv.sh LOG OUT}
OUT=${2:?usage: generate_he_core_severity_tsv.sh LOG OUT}

classify_row() {
    local rel=$1
    case "$rel" in
        cetta_tests/io_he_ext_assert_includes_unit.metta)
            printf '%s\t%s\t%s\n' \
                'helper-unit' 'low' \
                'assertIncludes now exists; the remaining difference is only whether the successful helper unit is surfaced in the grouped output.'
            ;;
        cetta_tests/io_he_ext_case_empty_branch.metta)
            printf '%s\t%s\t%s\n' \
                'control-shape' 'medium' \
                'Empty/default case routing still differs at the control-surface boundary.'
            ;;
        cetta_tests/spec_include_unit.metta)
            printf '%s\t%s\t%s\n' \
                'unit-aggregation' 'low' \
                'Successful top-level include still emits a unit bag where upstream currently suppresses it.'
            ;;
        cetta_tests/spec_translation_new_space_function_surface.metta)
            printf '%s\t%s\t%s\n' \
                'bag-order' 'low' \
                'Fresh-space atom order differs while the visible facts themselves match.'
            ;;
        cetta_tests/test_cverify_once_collapse_probe.metta)
            printf '%s\t%s\t%s\n' \
                'once-collapse-shape' 'medium' \
                'collapse(eval(...)) still differs on whether an explicit superpose wrapper is preserved.'
            ;;
        cetta_tests/test_math_ops.metta)
            printf '%s\t%s\t%s\n' \
                'numeric-surface' 'low' \
                'Some grounded math results still differ only by integer-vs-float output surface.'
            ;;
        cetta_tests/test_min_max_atom.metta)
            printf '%s\t%s\t%s\n' \
                'numeric-surface' 'low' \
                'min-atom/max-atom still differ only on mixed-list float output surface.'
            ;;
        cetta_tests/test_no_return_error.metta)
            printf '%s\t%s\t%s\n' \
                'oracle-quirk' 'medium' \
                'Upstream currently yields a fresh result variable here while PeTTa returns the spec-shaped NoReturn error.'
            ;;
        cetta_tests/test_trace_surface.metta)
            printf '%s\t%s\t%s\n' \
                'trace-format' 'low' \
                'trace! still differs only in how the first argument is rendered.'
            ;;
        *)
            printf '%s\t%s\t%s\n' \
                'unclassified' 'review' \
                'No canned severity note yet; inspect the fresh log side-by-side.'
            ;;
    esac
}

extract_rows() {
    local core_prefix='EXTENSION_OUTPUT_SHAPE [he-core] '
    local upstream_prefix='UPSTREAM_ONLY '
    local quirk_prefix='UPSTREAM_QUIRK '
    while IFS= read -r line; do
        case "$line" in
            'EXTENSION_OUTPUT_SHAPE [he-core] '*)
                printf '%s\n' "${line#"$core_prefix"}"
                ;;
            'UPSTREAM_ONLY '*)
                printf '%s\n' "${line#"$upstream_prefix"}"
                ;;
            'UPSTREAM_QUIRK '*)
                printf '%s\n' "${line#"$quirk_prefix"}"
                ;;
        esac
    done < "$LOG" | LC_ALL=C sort -u
}

{
    printf 'rel_path\tclass\tseverity\tnote\n'
    while IFS= read -r rel; do
        [ -n "$rel" ] || continue
        IFS=$'\t' read -r class severity note < <(classify_row "$rel")
        printf '%s\t%s\t%s\t%s\n' "$rel" "$class" "$severity" "$note"
    done < <(extract_rows)
} > "$OUT"
