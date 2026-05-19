#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/.." && pwd)
RUN_SH="$ROOT/run.sh"
TIME_BIN=${TIME_BIN:-/usr/bin/time}
TIMEOUT_SECONDS=${TIMEOUT_SECONDS:-60}
LIMIT_KB=${LIMIT_KB:-10485760}
SWIPL_STACK_LIMIT=${SWIPL_STACK_LIMIT:-4g}
SWIPL_THREADS=${SWIPL_THREADS:-false}
HE_METTA_BIN=${HE_METTA_BIN:-}
HE_ORACLE_HOME=${HE_ORACLE_HOME:-"$ROOT/.he-home"}
LIB_HE_ABS=$(cd -- "$ROOT/lib" && pwd)/lib_he

ulimit -v "$LIMIT_KB"
export SWIPL_STACK_LIMIT
export SWIPL_THREADS
mkdir -p "$HE_ORACLE_HOME"

status=0

run_case() {
    local label=$1
    shift
    printf '\n== %s ==\n' "$label"
    if timeout "$TIMEOUT_SECONDS" "$@" 2>&1; then
        printf 'PASS %s\n' "$label"
    else
        printf 'FAIL %s\n' "$label"
        status=1
    fi
}

run_case_env() {
    local label=$1
    shift
    printf '\n== %s ==\n' "$label"
    if timeout "$TIMEOUT_SECONDS" env "$@" 2>&1; then
        printf 'PASS %s\n' "$label"
    else
        printf 'FAIL %s\n' "$label"
        status=1
    fi
}

normalize_suite_output() {
    sed -e '/^MORK init: done$/d'
}

expect_output() {
    local label=$1
    local expected=$2
    shift 2
    local actual
    printf '\n== %s ==\n' "$label"
    if ! actual=$(timeout "$TIMEOUT_SECONDS" "$@" 2>&1); then
        printf '%s\n' "$actual"
        printf 'FAIL %s command\n' "$label"
        status=1
        return
    fi
    if diff -u <(normalize_suite_output < "$expected") \
              <(printf '%s\n' "$actual" | normalize_suite_output); then
        printf 'PASS %s\n' "$label"
    else
        printf 'FAIL %s output\n' "$label"
        status=1
    fi
}

expect_failure_contains() {
    local label=$1
    local needle=$2
    shift 2
    local actual
    printf '\n== %s ==\n' "$label"
    if actual=$(timeout "$TIMEOUT_SECONDS" "$@" 2>&1); then
        printf '%s\n' "$actual"
        printf 'FAIL %s command unexpectedly passed\n' "$label"
        status=1
        return
    fi
    if printf '%s\n' "$actual" | grep -Fq "$needle"; then
        printf 'PASS %s\n' "$label"
    else
        printf '%s\n' "$actual"
        printf 'FAIL %s output\n' "$label"
        status=1
    fi
}

bench_case() {
    local label=$1
    shift
    printf '\n== %s ==\n' "$label"
    if timeout "$TIMEOUT_SECONDS" "$TIME_BIN" -f '__TIME__ wall=%e rss_kb=%M exit=%x' "$@" 2>&1; then
        printf 'PASS %s\n' "$label"
    else
        printf 'FAIL %s\n' "$label"
        status=1
    fi
}

run_he_examples() {
    local f
    printf '\n== PeTTa --he examples/he_*.metta ==\n'
    for f in "$ROOT"/examples/he_*.metta; do
        printf '%s ' "${f#$ROOT/}"
        if timeout "$TIMEOUT_SECONDS" "$RUN_SH" --he "$f" --silent >/dev/null 2>&1; then
            printf 'PASS\n'
        else
            printf 'FAIL\n'
            status=1
        fi
    done
}

run_case 'PeTTa --he native surface' "$RUN_SH" --he "$ROOT/tests/he_native_surface.metta" --silent
run_case_env 'PeTTa --he direct hyperpose surface' SWIPL_THREADS=true "$RUN_SH" --he "$ROOT/tests/he_hyperpose_direct.metta" --silent
run_case 'PeTTa --he foreign callable heads' "$RUN_SH" --he "$ROOT/tests/he_foreign_callable.metta" --silent
run_case 'PeTTa --he executable spec core corpus' "$RUN_SH" --he "$ROOT/tests/he_spec_core.metta" --silent
run_case 'PeTTa --he executable spec type/error corpus' "$RUN_SH" --he "$ROOT/tests/he_spec_type_errors.metta" --silent
run_case 'PeTTa --he metta/evalc singleton collection regression' "$RUN_SH" --he "$ROOT/tests/he_metta_evalc_singleton_results.metta" --silent
run_case 'PeTTa --he arithmetic boundary' "$RUN_SH" --he "$ROOT/tests/he_profile_arithmetic.metta" --silent
run_case 'PeTTa --he equality callable lowering prime lane' "$RUN_SH" --he "$ROOT/tests/he_eq_callable_prime.metta" --silent
run_case 'PeTTa --he equality auto-type mismatch regression' "$RUN_SH" --he "$ROOT/tests/he_eq_autotype_error.metta" --silent
run_case 'PeTTa --he arithmetic helpers' "$RUN_SH" --he "$ROOT/tests/he_arithmetic_helpers.metta" --silent
run_case 'default PeTTa arithmetic unchanged' "$RUN_SH" "$ROOT/tests/petta_profile_arithmetic.metta" --silent
run_case 'default PeTTa lib_he remains a real import' "$RUN_SH" "$ROOT/tests/default_lib_he_real_import.metta" --silent
run_case 'default PeTTa does not expose HE arithmetic helpers' "$RUN_SH" "$ROOT/tests/default_no_he_helpers.metta" --silent
run_case 'PeTTa --he private user-head namespace' "$RUN_SH" --he "$ROOT/tests/he_private_namespace.metta" --silent
run_case 'PeTTa --he partial callables' "$RUN_SH" --he "$ROOT/tests/he_partial_application.metta" --silent
run_case 'PeTTa --he variable-head data' "$RUN_SH" --he "$ROOT/tests/he_variable_head_data.metta" --silent
run_case 'PeTTa --he source test surface' "$RUN_SH" --he "$ROOT/tests/he_spec_core.metta" --silent
run_case 'PeTTa --he source test get-type variable surface' "$RUN_SH" --he "$ROOT/tests/he_source_test_get_type_variable_surface.metta" --silent
run_case 'PeTTa --he assertEqualToEval surface' "$RUN_SH" --he "$ROOT/tests/he_assert_equal_to_eval_surface.metta" --silent
run_case 'PeTTa --he library import surface' "$RUN_SH" --he "$ROOT/tests/he_library_import_surface.metta" --silent
run_case 'PeTTa --he collapse tuple cartesian surface' "$RUN_SH" --he "$ROOT/tests/he_collapse_tuple_cartesian_surface.metta" --silent
run_case 'PeTTa --he dynamic callable returns' "$RUN_SH" --he "$ROOT/tests/he_dynamic_callable_return.metta" --silent
run_case 'PeTTa --he expression-head callables' "$RUN_SH" --he "$ROOT/tests/he_expression_head_callable.metta" --silent
run_case 'PeTTa --he destructured let expression patterns' "$RUN_SH" --he "$ROOT/tests/he_destructured_let_expr_pattern.metta" --silent
run_case 'PeTTa --he collapse count surfaces' "$RUN_SH" --he "$ROOT/tests/he_collapse_count_surface.metta" --silent
run_case 'PeTTa --he collapse streaming if/car characterization' "$RUN_SH" --he "$ROOT/tests/he_collapse_first_surface.metta" --silent
run_case 'PeTTa --he case-bound size-atom regression' "$RUN_SH" --he "$ROOT/tests/he_case_bound_size_atom_regression.metta" --silent
run_case 'PeTTa --he bind-visible laziness regression' "$RUN_SH" --he "$ROOT/tests/he_bind_visible_laziness_regression.metta" --silent
run_case 'PeTTa --he assertEqualMsg expected single evaluation' "$RUN_SH" --he "$ROOT/tests/he_assert_equal_msg_expected_single_eval.metta" --silent
run_case 'PeTTa --he match-once echo emptiness surface' "$RUN_SH" --he "$ROOT/tests/he_match_once_pattern_empty_surface.metta" --silent
run_case 'PeTTa --he identity-body match surface' "$RUN_SH" --he "$ROOT/tests/he_match_identity_body_surface.metta" --silent
run_case 'PeTTa --he callable tuple return surface' "$RUN_SH" --he "$ROOT/tests/he_callable_tuple_return_surface.metta" --silent
run_case 'PeTTa --he reverse function pattern surface' "$RUN_SH" --he "$ROOT/tests/he_reverse_function_pattern_surface.metta" --silent
run_case 'PeTTa --he data tuple preserves unknown heads' "$RUN_SH" --he "$ROOT/tests/he_data_tuple_preserves_unknown_head.metta" --silent
run_case 'PeTTa --he data tuple preserves list heads' "$RUN_SH" --he "$ROOT/tests/he_data_tuple_preserves_list_head.metta" --silent
run_case 'PeTTa --he variable functor data tuple surface' "$RUN_SH" --he "$ROOT/tests/he_variable_functor_data_tuple_surface.metta" --silent
run_case 'PeTTa --he constructor-like callable arg surface' "$RUN_SH" --he "$ROOT/tests/he_constructor_like_callable_arg_surface.metta" --silent
run_case 'PeTTa --he alpha equality evaluates args surface' "$RUN_SH" --he "$ROOT/tests/he_alpha_eq_evaluates_args_surface.metta" --silent
run_case 'PeTTa --he effectful tuple head regression' "$RUN_SH" --he "$ROOT/tests/he_effectful_data_tuple_head_regression.metta" --silent
run_case 'PeTTa --he unused binding recursive effect-only surface' "$RUN_SH" --he "$ROOT/tests/he_unused_binding_effect_only_recursive_surface.metta" --silent
run_case 'PeTTa --he unused binding recursive multivalue arg multiplicity' "$RUN_SH" --he "$ROOT/tests/he_unused_binding_recursive_multivalue_arg_preserves_multiplicity.metta" --silent
run_case 'PeTTa --he unused binding multivalue multiplicity regression' "$RUN_SH" --he "$ROOT/tests/he_unused_binding_multivalue_preserves_multiplicity.metta" --silent
run_case 'PeTTa --he singleton expression space patterns' "$RUN_SH" --he "$ROOT/tests/he_space_singleton_pattern.metta" --silent
run_case 'PeTTa --he collapse in data tuples' "$RUN_SH" --he "$ROOT/tests/he_collapse_in_data_tuple.metta" --silent
run_case 'PeTTa --he typed nondeterministic bool dispatch' "$RUN_SH" --he "$ROOT/tests/he_typed_nondet_bool.metta" --silent
run_case 'PeTTa --he foldl compatibility' "$RUN_SH" --he "$ROOT/tests/he_foldl_compat.metta" --silent
run_case 'PeTTa --he native range surface' "$RUN_SH" --he "$ROOT/tests/he_range_native_surface.metta" --silent
run_case 'PeTTa --he native move9 surface' "$RUN_SH" --he "$ROOT/tests/he_move9_native_surface.metta" --silent
run_case 'PeTTa --he bfs_all wrapper surface' "$RUN_SH" --he "$ROOT/tests/he_bfs_all_wrapper_surface.metta" --silent
run_case 'PeTTa --he bfs_all_limited wrapper surface' "$RUN_SH" --he "$ROOT/tests/he_bfs_all_limited_wrapper_surface.metta" --silent
run_case 'PeTTa --he native fold-nested surface' "$RUN_SH" --he "$ROOT/tests/he_fold_nested_native_surface.metta" --silent
run_case 'PeTTa --he native poly surface' "$RUN_SH" --he "$ROOT/tests/he_poly_native_surface.metta" --silent
run_case 'PeTTa --he foldl over collapse streaming surface' "$RUN_SH" --he "$ROOT/tests/he_foldl_collapse_stream_surface.metta" --silent
run_case 'PeTTa --he foldl over bound collapse streaming surface' "$RUN_SH" --he "$ROOT/tests/he_foldl_bound_collapse_stream_surface.metta" --silent
run_case 'PeTTa --he foldl over nested bound collapse streaming surface' "$RUN_SH" --he "$ROOT/tests/he_foldl_bound_collapse_nested_stream_surface.metta" --silent
run_case 'PeTTa --he eval-count length surface' "$RUN_SH" --he "$ROOT/tests/he_count_eval_expr_surface.metta" --silent
run_case 'PeTTa --he counted visible match surface' "$RUN_SH" --he "$ROOT/tests/he_count_visible_match_surface.metta" --silent
run_case 'PeTTa --he matespace count contract surface' "$RUN_SH" --he "$ROOT/tests/he_matespace_count_contract_surface.metta" --silent
run_case 'PeTTa --he matespace2 count contract surface' "$RUN_SH" --he "$ROOT/tests/he_matespace2_count_contract_surface.metta" --silent
run_case 'PeTTa --he peano count contract surface' "$RUN_SH" --he "$ROOT/tests/he_peano_count_contract_surface.metta" --silent
run_case 'PeTTa --he permutation count contract surface' "$RUN_SH" --he "$ROOT/tests/he_permutation_count_contract_surface.metta" --silent
run_case 'PeTTa --he scale indexing contract surface' "$RUN_SH" --he "$ROOT/tests/he_scale_indexing_contract_surface.metta" --silent
run_case 'PeTTa --he unique-space fold surface' "$RUN_SH" --he "$ROOT/tests/he_unique_space_fold_surface.metta" --silent
run_case 'PeTTa --he once/select compiled equation surface' "$RUN_SH" --he "$ROOT/tests/he_once_select_compiled_equation_surface.metta" --silent
run_case 'PeTTa --he higher-order curry full application' "$RUN_SH" --he "$ROOT/tests/he_higherorder_curry_call.metta" --silent
run_case 'PeTTa --he higher-order fmap empty constructor tail' "$RUN_SH" --he "$ROOT/tests/he_higherorder_fmap_empty_constructor.metta" --silent
run_case 'PeTTa --he lambda namespace surface' "$RUN_SH" --he "$ROOT/tests/he_lambda_namespace.metta" --silent
run_case 'PeTTa --he filter-atom function surface' "$RUN_SH" --he "$ROOT/tests/he_filter_atom_function_surface.metta" --silent
run_case 'PeTTa --he partial intrinsic equality surface' "$RUN_SH" --he "$ROOT/tests/he_partial_intrinsic_eq_surface.metta" --silent
run_case 'PeTTa --he logic-programming size constraint surface' "$RUN_SH" --he "$ROOT/tests/he_logicprogset_size_constraint_surface.metta" --silent
run_case 'PeTTa --he iterate compiled step surface' "$RUN_SH" --he "$ROOT/tests/he_iterate_compiled_step_surface.metta" --silent
run_case 'PeTTa --he chain cut side effects' "$RUN_SH" --he "$ROOT/tests/he_chain_cut_side_effect.metta" --silent
run_case 'PeTTa --he bound cut match surface' "$RUN_SH" --he "$ROOT/tests/he_cut_bound_match_surface.metta" --silent
run_case 'PeTTa --he add-unique-or-fail compatibility' "$RUN_SH" --he "$ROOT/tests/he_add_unique_or_fail_native.metta" --silent
run_case 'PeTTa --he exact repr membership surface' "$RUN_SH" --he "$ROOT/tests/he_space_exact_repr_surface.metta" --silent
run_case 'PeTTa --he functional queue native surface' "$RUN_SH" --he "$ROOT/tests/he_functional_queue_native_surface.metta" --silent
run_case 'PeTTa --he new-space in function expression position' "$RUN_SH" --he "$ROOT/tests/he_new_space_function_surface.metta" --silent
run_case 'PeTTa --he compiled function multivalue order' "$RUN_SH" --he "$ROOT/tests/he_compiled_function_multivalue_order.metta" --silent
run_case 'PeTTa --he atomic space match shape' "$RUN_SH" --he "$ROOT/tests/he_space_atomic_match_shape.metta" --silent
run_case 'PeTTa --he malformed with-space-snapshot passthrough' "$RUN_SH" --he "$ROOT/tests/he_with_space_snapshot_passthrough.metta" --silent
run_case 'PeTTa --he effectful superpose over spaces' "$RUN_SH" --he "$ROOT/tests/he_superpose_eval_side_effects.metta" --silent
expect_output 'PeTTa --he native helper arity errors' \
    "$ROOT/tests/expected/he_native_helper_arity_errors.expected" \
    "$RUN_SH" --he "$ROOT/tests/he_native_helper_arity_errors.metta" --silent
run_case 'PeTTa --he non-native arity errors' "$RUN_SH" --he "$ROOT/tests/he_non_native_arity_errors.metta" --silent
run_case 'PeTTa --he numeric edge cases' "$RUN_SH" --he "$ROOT/tests/he_numeric_edge_cases.metta" --silent
run_case 'PeTTa --he Empty visibility rules' "$RUN_SH" --he "$ROOT/tests/he_empty_visibility.metta" --silent
run_case 'PeTTa --he Empty case default branch' "$RUN_SH" --he "$ROOT/tests/he_case_empty_branch.metta" --silent
run_case 'PeTTa --he ordered space surfaces' "$RUN_SH" --he "$ROOT/tests/he_ordered_space_surface.metta" --silent
run_case 'PeTTa --he string/debug/sealed surfaces' "$RUN_SH" --he "$ROOT/tests/he_string_debug_surface.metta" --silent
run_case 'PeTTa --he assertIncludes helper surface' "$RUN_SH" --he "$ROOT/tests/he_assert_includes_surface.metta" --silent
run_case 'PeTTa --he eval preserves explicit superpose surface' "$RUN_SH" --he "$ROOT/tests/he_eval_superpose_surface.metta" --silent
run_case 'PeTTa --he quoted eval code-input surface' "$RUN_SH" --he "$ROOT/tests/he_eval_quoted_expr_surface.metta" --silent
run_case 'PeTTa --he unique evaluates argument surface' "$RUN_SH" --he "$ROOT/tests/he_unique_evaluates_argument_surface.metta" --silent
run_case 'PeTTa --he function NoReturn surface' "$RUN_SH" --he "$ROOT/tests/he_no_return_error_surface.metta" --silent
expect_output 'PeTTa --he NoReturn harness policy guardrail' \
    "$ROOT/tests/expected/he_no_return_policy_guardrail.expected" \
    "$ROOT/tests/tools/check_no_return_policy_guardrail.sh"
run_case 'PeTTa --he add-atoms surface' "$RUN_SH" --he "$ROOT/tests/he_add_atoms_surface.metta" --silent
run_case 'PeTTa --he ground recursive memo surface' "$RUN_SH" --he "$ROOT/tests/he_ground_recursive_memo_surface.metta" --silent
run_case 'PeTTa --he textual parser surface' "$RUN_SH" --he "$ROOT/tests/he_textual_parser_surface.metta" --silent
run_case 'PeTTa --he zero-arg atom-head callable expressions' "$RUN_SH" --he "$ROOT/tests/he_zero_arg_atom_head_callable.metta" --silent
run_case 'PeTTa --he import cycle transactional rollback' "$RUN_SH" --he "$ROOT/tests/he_import_cycle_transactional.metta" --silent
run_case 'PeTTa --he quote/capture surface' "$RUN_SH" --he "$ROOT/tests/he_quote_capture_surface.metta" --silent
run_case 'PeTTa --he specialization type facts' "$RUN_SH" --he "$ROOT/tests/he_specialization_type_facts.metta" --silent
run_case 'PeTTa --he typechain cache invalidation' "$RUN_SH" --he "$ROOT/tests/he_typechain_cache_invalidation.metta" --silent
run_case 'PeTTa --he dynamic equation metadata removal' "$RUN_SH" --he "$ROOT/tests/he_dynamic_equation_metadata_remove.metta" --silent
run_case 'PeTTa --he runtime callable negative cache invalidation' "$RUN_SH" --he "$ROOT/tests/he_runtime_callable_negative_cache_invalidation.metta" --silent
run_case 'PeTTa --he nested match effect tuple surface' "$RUN_SH" --he "$ROOT/tests/he_matchnested_effect_tuple_surface.metta" --silent
run_case 'PeTTa --he get-type data tuples' "$RUN_SH" --he "$ROOT/tests/he_get_type_data_tuple.metta" --silent
run_case 'PeTTa --he composite wildcard type matching' "$RUN_SH" --he "$ROOT/tests/he_match_types_composite_wildcard.metta" --silent
run_case 'PeTTa --he polymorphic return alternate type' "$RUN_SH" --he "$ROOT/tests/he_polymorphic_return_alternate_type.metta" --silent
run_case 'PeTTa --he inverse constructor output patterns' "$RUN_SH" --he "$ROOT/tests/he_inverse_constructor_output.metta" --silent
run_case 'PeTTa --he inverse nested constructor output patterns' "$RUN_SH" --he "$ROOT/tests/he_inverse_nested_constructor_output.metta" --silent
expect_failure_contains 'default PeTTa user-head/SWI collision is characterized' \
    'No permission to modify static procedure `length/2' \
    "$RUN_SH" "$ROOT/tests/petta_default_collision_expected_failure.metta" --silent

run_he_examples

bench_case 'PeTTa --he direct recursion benchmark' "$RUN_SH" --he "$ROOT/tests/bench_he_direct_recursion.metta" --silent
bench_case 'PeTTa --he native minimalmetta benchmark' "$RUN_SH" --he "$ROOT/tests/bench_he_minimalmetta_native.metta" --silent
bench_case 'PeTTa --he legacy he_minimalmetta example' "$RUN_SH" --he "$ROOT/examples/he_minimalmetta.metta" --silent

run_case 'PeTTa --he relative lib_he ordinary import' "$RUN_SH" --he <(printf '%s\n' \
    '!(import! &self ../lib/lib_he)' \
    '!(test (assertEqual (+ 1 2) 3) ())') --silent

run_case 'PeTTa --he absolute lib_he ordinary import' "$RUN_SH" --he <(printf '%s\n' \
    "!(import! &self \"$LIB_HE_ABS\")" \
    '!(test (assertEqual (+ 1 2) 3) ())') --silent

expect_output 'PeTTa --he oracle smoke expected output' \
    "$ROOT/tests/expected/he_oracle_smoke.petta.expected" \
    "$RUN_SH" --he "$ROOT/tests/he_oracle_smoke.metta" --silent

expect_output 'PeTTa --he trace surface output' \
    "$ROOT/tests/expected/he_trace_surface.expected" \
    "$RUN_SH" --he "$ROOT/tests/he_trace_surface.metta" --silent

expect_output 'PeTTa --he include success suppresses top-level unit bag' \
    "$ROOT/tests/expected/he_include_unit_surface.expected" \
    "$RUN_SH" --he "$ROOT/tests/he_include_unit_surface.metta" --silent

if [ -n "$HE_METTA_BIN" ] || command -v metta >/dev/null 2>&1; then
    if [ -z "$HE_METTA_BIN" ]; then
        HE_METTA_BIN=$(command -v metta)
    fi
    expect_output 'upstream HE oracle smoke expected output' \
        "$ROOT/tests/expected/he_oracle_smoke.upstream-he.expected" \
        env HOME="$HE_ORACLE_HOME" "$HE_METTA_BIN" "$ROOT/tests/he_oracle_smoke.metta"
else
    printf '\n== upstream HE oracle smoke expected output ==\n'
    printf 'SKIP upstream HE oracle smoke; set HE_METTA_BIN=/path/to/metta to enable it.\n'
fi

exit "$status"
