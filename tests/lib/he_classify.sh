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

strip_metta_comments() {
    sed '/^[[:space:]]*;/d' "$1"
}

cetta_uses_nonpetta_he_extension() {
    local file=$1
    local pattern='[(][[:space:]]*module-profile[[:space:]]+he_extended([[:space:])]|$)|[(][[:space:]]*import!?[[:space:]]+&self[[:space:]]+(mork|fs|str|system)([[:space:])]|$)|[(][[:space:]]*include[[:space:]]+(mork|fs|str|system)([[:space:])]|$)|[(][[:space:]]*(runtime-stats!|reset-runtime-stats!|collect|reduce|fold|foldl|fold-by-key|select|search-policy|space-engine|space-match-backend|space-set-match-backend|module-provider-locator-kind|module-mount-source|size-atom)([[:space:])]|$)|(mork:|fs-|str-|system-)'
    strip_metta_comments "$file" | grep -Eq "$pattern"
}

he_corpus_skip_reason() {
    local rel=$1
    local file=$2

    case "$rel" in
        */_tmp_*.metta|_tmp_*.metta)
            printf '%s\n' 'cetta-fixture'
            return 0
            ;;
        cetta_tests/spec_module_inventory.metta|\
        cetta_tests/spec_print_mods_inventory.metta|\
        cetta_tests/support/profile_compile_module_inventory.metta|\
        cetta_tests/support/profile_module_inventory_runtime.metta)
            printf '%s\n' 'cetta-admin'
            return 0
            ;;
        hyperon_scripts/f1_imports.metta)
            printf '%s\n' 'he-no-python-env'
            return 0
            ;;
        cetta_tests/profile_he_prime_dependent_binders_compat.metta|\
        cetta_tests/support/import_parse_fail/module.metta|\
        cetta_tests/support/git_module_seed/*.metta|\
        cetta_tests/support/import_*/**/*.metta|\
        cetta_tests/support/import_*/*.metta|\
        cetta_tests/support/pln_portable/*.metta)
            printf '%s\n' 'cetta-fixture'
            return 0
            ;;
        cetta_tests/bench_*.metta|\
        cetta_tests/profile_*.metta|\
        cetta_tests/bio_*.metta|\
        cetta_tests/discovered_patterns_*.metta|\
        cetta_tests/eqtl_for_mining.metta|\
        cetta_tests/support/runtime_witness_*.metta|\
        cetta_tests/tail_recursion_deep.metta)
            printf '%s\n' 'cetta-workload'
            return 0
            ;;
        cetta_tests/spec_profile*.metta|\
        cetta_tests/support/profile_*.metta|\
        cetta_tests/support/runtime_stats_cli_probe.metta|\
        cetta_tests/test_hash_space*.metta|\
        cetta_tests/test_queue_space*.metta|\
        cetta_tests/test_stack_space*.metta|\
        cetta_tests/test_namespace_sugar_guardrails.metta|\
        cetta_tests/test_collect*.metta|\
        cetta_tests/test_fold*.metta|\
        cetta_tests/test_reduce*.metta|\
        cetta_tests/test_search_policy*.metta|\
        cetta_tests/test_select*.metta|\
        cetta_tests/test_runtime_stats*.metta|\
        cetta_tests/test_closed_stream*.metta|\
        cetta_tests/test_cverify_once_collapse_probe.metta|\
        cetta_tests/test_space_engine*.metta|\
        cetta_tests/test_step_space*.metta|\
        cetta_tests/test_stdlib_helper_tranche.metta|\
        cetta_tests/test_once.metta|\
        cetta_tests/test_fs*.metta|\
        cetta_tests/test_str*.metta|\
        cetta_tests/test_system*.metta|\
        cetta_tests/test_list_surface.metta|\
        cetta_tests/test_clist_surface.metta|\
        cetta_tests/test_*mork*.metta|\
        cetta_tests/test_mm2*.metta|\
        cetta_tests/test_new_space_mork_surface.metta|\
        cetta_tests/test_import_act_module_surface.metta|\
        cetta_tests/test_import_mm2*.metta|\
        cetta_tests/test_include_mm2_space_target.metta|\
        cetta_tests/test_module_inventory*.metta|\
        cetta_tests/test_pathmap*.metta)
            printf '%s\n' 'cetta-nonpetta-he-extension'
            return 0
            ;;
    esac

    if [[ "$rel" == cetta_tests/* ]] && cetta_uses_nonpetta_he_extension "$file"; then
        printf '%s\n' 'cetta-nonpetta-he-extension'
        return 0
    fi

    return 1
}

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
        hyperon_scripts/f1_eval_match_probe.metta)
            category=presentation
            div=DIV-004
            ;;
        cetta_tests/test_print_alternatives.metta|\
        cetta_tests/test_print_nondet_probe.metta)
            category=format-only
            div=DIV-004
            ;;
        support/foreign_py_simple_probe.metta|*/support/foreign_py_simple_probe.metta)
            category=callable-head-gap
            div=DIV-008
            ;;
        support/oracle_invertfunction_returned_head_probe.metta|*/support/oracle_invertfunction_returned_head_probe.metta|support/oracle_invertfunction_returned_head_structural_probe.metta|*/support/oracle_invertfunction_returned_head_structural_probe.metta)
            category=support-more
            div=DIV-009
            ;;
        *spec_profile_collect_extension.metta|*spec_profile_count_atoms.metta|*spec_profile_fold_by_key_extension.metta|*spec_profile_fold_extension.metta|*spec_profile_foldl_extension.metta|*spec_profile_once_alias_extension.metta|*spec_profile_reduce_extension.metta|*spec_profile_select_extension.metta|*spec_profile_size_extension.metta|*spec_profile_space_set_match_backend_extension.metta|cetta_tests/test_disc_trie.metta|cetta_tests/test_py_ops_surface.metta|cetta_tests/spec_translation_delete_space_surface.metta|support/profile_module_inventory_runtime.metta|*/support/profile_module_inventory_runtime.metta|support/pln_portable_min_probe.metta|*/support/pln_portable_min_probe.metta|support/oracle_evalcustom_probe.metta|*/support/oracle_evalcustom_probe.metta|support/oracle_import_syntax_probe.metta|*/support/oracle_import_syntax_probe.metta|support/oracle_import_syntax_deep_probe.metta|*/support/oracle_import_syntax_deep_probe.metta|support/oracle_once_match_env_probe.metta|*/support/oracle_once_match_env_probe.metta)
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
        cetta_tests/test_import_cycle.metta|\
        cetta_tests/test_import_foreign_pkg_error.metta|\
        cetta_tests/test_import_parse_failure.metta|\
        cetta_tests/test_import_transaction.metta|\
        cetta_tests/test_search_machine_config_variant_backchain.metta|\
        support/import*|*/support/import*|support/*/import*|*/support/*/import*|support/petta_import_walk/*|*/support/petta_import_walk/*|*oracle_import_syntax*|*oracle_lib_he_assert_probe*)
            category=import-compat
            div=DIV-003
            ;;
        support/bio_*|*/support/bio_*|support/*wmpln*|*/support/*wmpln*|support/pln_*|*/support/pln_*|support/prepare_*|*/support/prepare_*)
            category=workload
            div=DIV-002
            ;;
        support/*|*/support/*)
            category=support-probe
            div=DIV-002
            ;;
    esac

    if [ "$status" = same ]; then
        div=-
    fi

    printf '%s\t%s\n' "$category" "$div"
}

upstream_only_kind() {
    local rel=$1
    case "$rel" in
        cetta_tests/test_no_return_error.metta)
            # Policy choice: keep the HE-spec-shaped NoReturn surface even
            # though current upstream HE leaks a fresh variable here. The
            # corpus runner should keep this visible without calling it a
            # PeTTa regression.
            printf '%s\n' 'oracle-quirk'
            ;;
        *)
            printf '%s\n' 'regression'
            ;;
    esac
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
