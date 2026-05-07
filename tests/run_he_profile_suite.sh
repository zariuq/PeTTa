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
    if diff -u "$expected" <(printf '%s\n' "$actual"); then
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
run_case 'PeTTa --he translated PeTTa test compatibility' "$RUN_SH" --he "$ROOT/tests/he_petta_test_compat.metta" --silent
run_case 'PeTTa --he dynamic callable returns' "$RUN_SH" --he "$ROOT/tests/he_dynamic_callable_return.metta" --silent
run_case 'PeTTa --he expression-head callables' "$RUN_SH" --he "$ROOT/tests/he_expression_head_callable.metta" --silent
run_case 'PeTTa --he destructured let expression patterns' "$RUN_SH" --he "$ROOT/tests/he_destructured_let_expr_pattern.metta" --silent
run_case 'PeTTa --he singleton expression space patterns' "$RUN_SH" --he "$ROOT/tests/he_space_singleton_pattern.metta" --silent
run_case 'PeTTa --he collapse in data tuples' "$RUN_SH" --he "$ROOT/tests/he_collapse_in_data_tuple.metta" --silent
run_case 'PeTTa --he typed nondeterministic bool dispatch' "$RUN_SH" --he "$ROOT/tests/he_typed_nondet_bool.metta" --silent
run_case 'PeTTa --he foldl compatibility' "$RUN_SH" --he "$ROOT/tests/he_foldl_compat.metta" --silent
run_case 'PeTTa --he higher-order curry full application' "$RUN_SH" --he "$ROOT/tests/he_higherorder_curry_call.metta" --silent
run_case 'PeTTa --he higher-order fmap empty constructor tail' "$RUN_SH" --he "$ROOT/tests/he_higherorder_fmap_empty_constructor.metta" --silent
run_case 'PeTTa --he chain cut side effects' "$RUN_SH" --he "$ROOT/tests/he_chain_cut_side_effect.metta" --silent
run_case 'PeTTa --he add-unique-or-fail compatibility' "$RUN_SH" --he "$ROOT/tests/he_add_unique_or_fail_native.metta" --silent
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
run_case 'PeTTa --he function NoReturn surface' "$RUN_SH" --he "$ROOT/tests/he_no_return_error_surface.metta" --silent
expect_output 'PeTTa --he NoReturn harness policy guardrail' \
    "$ROOT/tests/expected/he_no_return_policy_guardrail.expected" \
    "$ROOT/tests/tools/check_no_return_policy_guardrail.sh"
run_case 'PeTTa --he add-atoms surface' "$RUN_SH" --he "$ROOT/tests/he_add_atoms_surface.metta" --silent
run_case 'PeTTa --he textual parser surface' "$RUN_SH" --he "$ROOT/tests/he_textual_parser_surface.metta" --silent
run_case 'PeTTa --he zero-arg atom-head callable expressions' "$RUN_SH" --he "$ROOT/tests/he_zero_arg_atom_head_callable.metta" --silent
run_case 'PeTTa --he import cycle transactional rollback' "$RUN_SH" --he "$ROOT/tests/he_import_cycle_transactional.metta" --silent
run_case 'PeTTa --he quote/capture surface' "$RUN_SH" --he "$ROOT/tests/he_quote_capture_surface.metta" --silent
run_case 'PeTTa --he specialization type facts' "$RUN_SH" --he "$ROOT/tests/he_specialization_type_facts.metta" --silent
run_case 'PeTTa --he typechain cache invalidation' "$RUN_SH" --he "$ROOT/tests/he_typechain_cache_invalidation.metta" --silent
run_case 'PeTTa --he dynamic equation metadata removal' "$RUN_SH" --he "$ROOT/tests/he_dynamic_equation_metadata_remove.metta" --silent
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
