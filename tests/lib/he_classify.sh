#!/usr/bin/env bash
# tests/lib/he_classify.sh
#
# Shared helpers used by both tests/run_he_oracle_diff.sh and
# tests/run_he_corpus_bundle.sh. Keep these two runners reading from the same
# normalization and classification logic so they cannot drift.
#
# Contract expected from the sourcing script:
#   - LIMIT_KB and TIMEOUT_SECONDS env vars must be set before calling
#     run_capture.
#   - Before calling remember_category the caller must declare:
#       declare -A cat_total=() cat_same=() cat_diff=()
#       categories=()

[ "${__HE_CLASSIFY_SH_SOURCED:-}" = 1 ] && return 0
__HE_CLASSIFY_SH_SOURCED=1

normalize_output() {
    sed -e '/^MORK init:/d' \
        -e '/^;<stdin>:[0-9][0-9]*: SyntaxWarning:/d' \
        -e 's/^\[()\]$/true/' \
        -e 's/^()$/true/' \
        -e 's/^\[True\]$/true/' \
        -e 's/^\[\([^][,]*\)\]$/\1/' \
        -e 's/GroundingSpace-0x[0-9A-Fa-f][0-9A-Fa-f]*/GroundingSpace/g' \
        -e 's/[[:space:]]*$//'
}

presentation_key() {
    # Aggressive normalizer used ONLY for diff salvage: if both outputs
    # reduce to the same string under this, the original difference is
    # presentation-only (variable renaming, space-handle hex, singleton
    # bracket wrap). Do not use this for semantic comparison.
    printf '%s\n' "$1" |
        sed -e 's/\\n/\
/g' \
            -e 's/^\[\(.*\)\]$/\1/' \
            -e 's/GroundingSpace-0x[0-9A-Fa-f][0-9A-Fa-f]*/GroundingSpace/g' \
            -e 's/\$[^][(){}[:space:],]*/$VAR/g' \
            -e 's/ModuleSpace(GroundingSpace-top)/&self/g' \
            -e 's/[[:space:]]*$//' |
        sed ':a;N;$!ba;s/\n/\\n/g'
}

classify_case() {
    local rel=$1
    local status=$2
    local he_out=$3
    local petta_out=$4
    local category=he-core
    local div=-

    # For diffs, check presentation equivalence FIRST. If the two outputs
    # reduce to the same string under alpha/var-renaming and bracket
    # normalization, categorize as presentation regardless of file path.
    # This must run before file-path classification or we mis-bucket
    # spec-adjacent files that differ only by variable rendering.
    if [ "$status" = diff ] && \
       [ "$(presentation_key "$he_out")" = "$(presentation_key "$petta_out")" ]; then
        printf 'presentation\tDIV-004\n'
        return
    fi

    case "$rel" in
        *spec_profile_atom_introspection_extension.metta|*test_pretty_vars_surface.metta|*test_pretty_namespaces_surface.metta)
            category=format-only
            div=DIV-004
            ;;
        */support/foreign_py_simple_probe.metta)
            category=callable-head-gap
            div=DIV-008
            ;;
        */support/oracle_invertfunction_returned_head_probe.metta|*/support/oracle_invertfunction_returned_head_structural_probe.metta)
            category=support-more
            div=DIV-009
            ;;
        *spec_profile_collect_extension.metta|*spec_profile_count_atoms.metta|*spec_profile_fold_by_key_extension.metta|*spec_profile_fold_extension.metta|*spec_profile_foldl_extension.metta|*spec_profile_once_alias_extension.metta|*spec_profile_reduce_extension.metta|*spec_profile_select_extension.metta|*spec_profile_size_extension.metta|*spec_profile_space_set_match_backend_extension.metta|*/support/profile_module_inventory_runtime.metta|*/support/pln_portable_min_probe.metta|*/support/oracle_evalcustom_probe.metta|*/support/oracle_import_syntax_probe.metta|*/support/oracle_import_syntax_deep_probe.metta|*/support/oracle_once_match_env_probe.metta)
            category=extension-helper-surface
            div=DIV-010
            ;;
        */g1_docs.metta|*/he_g1_docs.metta)
            category=doc-surface
            div=DIV-005
            ;;
        *d5_auto_types.metta)
            category=type-behavior
            div=DIV-007
            ;;
        *e2_states.metta|*e3_match_states.metta)
            category=state-surface
            div=DIV-006
            ;;
        *spec_profile*|*profile_*|*runtime_stats*|*closed_stream*|*pathmap*|*mork*|*space_set*|*space_type*|*module_inventory*|*pretty_*|*select*|*search_policy*|*fold*|*collect*|*reduce*|*test_imported*|*test_match_chain_imported*)
            category=extension
            div=DIV-002
            ;;
        */support/import*|*/support/*/import*|*/support/petta_import_walk/*|*oracle_import_syntax*|*oracle_lib_he_assert_probe*)
            category=import-compat
            div=DIV-003
            ;;
        */support/bio_*|*/support/*wmpln*|*/support/pln_*|*/support/prepare_*)
            category=workload
            div=DIV-002
            ;;
        */support/*)
            category=support-probe
            div=DIV-002
            ;;
    esac

    if [ "$status" = same ]; then
        div=-
    fi

    printf '%s\t%s\n' "$category" "$div"
}

run_capture() {
    local label=$1
    shift
    local out
    set +e
    if [ "$label" = he ] && [ -n "${HE_ORACLE_HOME:-}" ]; then
        out=$(ulimit -v "$LIMIT_KB" && HOME="$HE_ORACLE_HOME" timeout "$TIMEOUT_SECONDS" "$@" 2>&1)
    else
        out=$(ulimit -v "$LIMIT_KB" && timeout "$TIMEOUT_SECONDS" "$@" 2>&1)
    fi
    local rc=$?
    set -e
    printf '%s\t%s\n' "$rc" "$(printf '%s\n' "$out" | normalize_output | sed ':a;N;$!ba;s/\n/\\n/g')"
}

remember_category() {
    local category=$1
    local status=$2
    if [ -z "${cat_total[$category]+x}" ]; then
        categories+=("$category")
        cat_total[$category]=0
        cat_same[$category]=0
        cat_diff[$category]=0
    fi
    cat_total[$category]=$((cat_total[$category] + 1))
    case "$status" in
        same) cat_same[$category]=$((cat_same[$category] + 1)) ;;
        diff) cat_diff[$category]=$((cat_diff[$category] + 1)) ;;
    esac
}
