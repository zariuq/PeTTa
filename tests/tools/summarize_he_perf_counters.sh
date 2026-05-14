#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd -- "$(dirname -- "$0")/../.." && pwd)
LOG_DIR=${LOG_DIR:-"$ROOT/.he-logs/profile_he_remaining"}
OUT=${OUT:-"$LOG_DIR/he_perf_counter_summary.tsv"}

usage() {
    cat <<'EOF'
Usage: tests/tools/summarize_he_perf_counters.sh

Reads profile_he_remaining/*.profile.txt counter blocks and writes a TSV summary.

Environment:
  LOG_DIR  directory containing *.profile.txt logs
  OUT      output TSV path
EOF
}

if [ "${1:-}" = "-h" ] || [ "${1:-}" = "--help" ]; then
    usage
    exit 0
fi

mkdir -p "$(dirname -- "$OUT")"
TMP_ROWS=$(mktemp "$LOG_DIR/.he_perf_counter_summary_rows.XXXXXX")
trap 'rm -f "$TMP_ROWS"' EXIT

for log in "$LOG_DIR"/*.profile.txt; do
    [ -f "$log" ] || continue
    case_name=$(basename "$log" .profile.txt)
    awk -v case_name="$case_name" '
        function counter(name) {
            return (name in counts) ? counts[name] : 0
        }
        function ratio(num, den) {
            if (den == 0) return "0.000"
            return sprintf("%.3f", num / den)
        }
        BEGIN {
            in_block = 0
            exit_code = ""
        }
        /^HE_PERF_COUNTERS_BEGIN$/ { in_block = 1; next }
        /^HE_PERF_COUNTERS_END$/ { in_block = 0; next }
        /^exit=/ {
            split($0, a, "=")
            exit_code = a[2]
            next
        }
        in_block && NF >= 2 {
            counts[$1] = $2
        }
        END {
            compiled = counter("compiled_equation_goal_result_collections")
            raw = counter("compiled_equation_goal_raw_rows")
            visible = counter("compiled_equation_goal_visible_rows")
            single_direct_calls = counter("compiled_equation_goal_single_result_calls")
            single_direct_hits = counter("compiled_equation_goal_single_direct_hits")
            single_collect_fallbacks = counter("compiled_equation_goal_single_collect_fallbacks")
            multi_shape_calls = counter("compiled_equation_goal_multi_shape_calls")
            multi_shape_hits = counter("compiled_equation_goal_multi_shape_hits")
            visible_stream_calls = counter("compiled_equation_goal_visible_stream_calls")
            visible_stream_hits = counter("compiled_equation_goal_visible_stream_hits")
            first_visible_calls = counter("compiled_equation_goal_first_visible_calls")
            first_visible_raw = counter("compiled_equation_goal_first_visible_raw_rows")
            first_visible_visible = counter("compiled_equation_goal_first_visible_visible_rows")
            typed_calls = counter("typed_visible_or_all_calls")
            typed_replays = counter("typed_visible_or_all_replays")
            collect_calls = counter("collect_visible_results_calls")
            collect_rows = counter("collect_visible_results_rows")
            bind_calls = counter("bind_visible_results_calls")
            bind_rows = counter("bind_visible_results_rows")
            once_calls = counter("once_visible_result_calls")
            count_calls = counter("count_visible_results_calls")
            count_rows = counter("count_visible_results_rows")
            count_match_fast_hits = counter("count_visible_results_match_fast_hits")
            count_eval_calls = counter("count_eval_expr_calls")
            count_eval_fast_hits = counter("count_eval_expr_fast_hits")
            count_eval_range_hits = counter("count_eval_expr_range_hits")
            count_eval_mapflat_hits = counter("count_eval_expr_mapflat_hits")
            fold_calls = counter("fold_visible_results_calls")
            fold_rows = counter("fold_visible_results_rows")
            space_exact_calls = counter("space_exact_member_calls")
            space_exact_hits = counter("space_exact_member_hits")
            space_exact_repr_trie_calls = counter("space_exact_repr_trie_calls")
            space_exact_repr_trie_hits = counter("space_exact_repr_trie_hits")
            space_add_unique_public_calls = counter("space_add_unique_public_calls")
            space_add_unique_public_added = counter("space_add_unique_public_added")
            space_add_unique_public_duplicate_skips = counter("space_add_unique_public_duplicate_skips")
            space_match_count_calls = counter("space_match_count_calls")
            space_match_count_key_hits = counter("space_match_count_key_hits")
            space_match_count_scan_rows = counter("space_match_count_scan_rows")
            space_candidate_hits = counter("space_candidate_index_hits")
            space_candidate_fallbacks = counter("space_candidate_scan_fallbacks")
            space_atom_scan_rows = counter("space_atom_scan_rows")
            runtime_callable_checks = counter("runtime_callable_head_checks")
            runtime_callable_cache_hits = counter("runtime_callable_head_cache_hits")
            runtime_callable_negative_cache_hits = counter("runtime_callable_head_negative_cache_hits")
            runtime_callable_predicate_hits = counter("runtime_callable_head_predicate_hits")
            runtime_callable_meta_hits = counter("runtime_callable_head_meta_hits")
            runtime_callable_partial_hits = counter("runtime_callable_head_partial_hits")
            runtime_noncallable_checks = counter("runtime_noncallable_head_checks")
            runtime_noncallable_list_data_hits = counter("runtime_noncallable_head_list_data_hits")
            runtime_noncallable_obvious_hits = counter("runtime_noncallable_head_obvious_atom_hits")
            runtime_noncallable_negative_cache_fast_paths = counter("runtime_noncallable_head_negative_cache_fast_paths")
            runtime_noncallable_list_data_fast_paths = counter("runtime_noncallable_head_list_data_fast_paths")
            runtime_noncallable_scalar_fast_paths = counter("runtime_noncallable_head_scalar_fast_paths")
            runtime_arg_raw_data_fast_paths = counter("runtime_arg_raw_data_fast_paths")
            var_head_atom_direct_hits = counter("var_head_atom_direct_hits")
            var_head_partial_direct_hits = counter("var_head_partial_direct_hits")
            var_head_direct_fallbacks = counter("var_head_direct_fallbacks")
            unknown_head_negative_cache_fast_paths = counter("unknown_head_negative_cache_fast_paths")
            partial_plan_cache_hits = counter("partial_apply_dispatch_plan_cache_hits")
            partial_plan_cache_stores = counter("partial_apply_dispatch_plan_cache_stores")
            partial_direct_compiled_user_hits = counter("partial_apply_direct_compiled_user_hits")
            partial_direct_runtime_predicate_hits = counter("partial_apply_direct_runtime_predicate_hits")
            partial_direct_zero_arg_equation_hits = counter("partial_apply_direct_zero_arg_equation_hits")
            partial_direct_fallbacks = counter("partial_apply_direct_fallbacks")
            native_empty_queue_hits = counter("native_datastructure_empty_queue_hits")
            native_enqueue_hits = counter("native_datastructure_enqueue_hits")
            native_dequeue_hits = counter("native_datastructure_dequeue_hits")
            native_add_unique_hits = counter("native_datastructure_add_unique_hits")
            native_range_calls = counter("native_range_calls")
            native_range_hits = counter("native_range_hits")
            native_deep_nest_calls = counter("native_deep_nest_calls")
            native_deep_nest_hits = counter("native_deep_nest_hits")
            native_fold_nested_sum_calls = counter("native_fold_nested_sum_calls")
            native_fold_nested_sum_hits = counter("native_fold_nested_sum_hits")
            native_queue_search_calls = counter("native_queue_search_calls")
            native_queue_search_nodes = counter("native_queue_search_nodes")
            native_queue_search_neighbor_rows = counter("native_queue_search_neighbor_rows")
            effect_only_expr_calls = counter("effect_only_expr_calls")
            effect_only_fun_direct_hits = counter("effect_only_fun_direct_hits")
            effect_only_native_fun_hits = counter("effect_only_native_fun_hits")
            effect_only_native_branching_calls = counter("effect_only_native_branching_calls")
            effect_only_self_add_atom_batches = counter("effect_only_self_add_atom_batches")
            effect_only_self_add_atom_batch_terms = counter("effect_only_self_add_atom_batch_terms")
            effect_only_self_add_atom_data_count_batches = counter("effect_only_self_add_atom_data_count_batches")
            effect_only_self_add_atom_data_count_batch_terms = counter("effect_only_self_add_atom_data_count_batch_terms")
            printf "%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s\t%s\t%d\t%d\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\n",
                   case_name,
                   exit_code,
                   compiled,
                   raw,
                   visible,
                   single_direct_calls,
                   single_direct_hits,
                   single_collect_fallbacks,
                   multi_shape_calls,
                   multi_shape_hits,
                   visible_stream_calls,
                   visible_stream_hits,
                   first_visible_calls,
                   first_visible_raw,
                   first_visible_visible,
                   ratio(raw, compiled),
                   ratio(visible, compiled),
                   typed_calls,
                   typed_replays,
                   ratio(typed_replays, typed_calls),
                   collect_calls,
                   collect_rows,
                   bind_calls,
                   bind_rows,
                   once_calls,
                   count_calls,
                   count_rows,
                   count_match_fast_hits,
                   count_eval_calls,
                   count_eval_fast_hits,
                   count_eval_range_hits,
                   count_eval_mapflat_hits,
                   fold_calls,
                   fold_rows,
                   space_exact_calls,
                   space_exact_hits,
                   space_exact_repr_trie_calls,
                   space_exact_repr_trie_hits,
                   space_add_unique_public_calls,
                   space_add_unique_public_added,
                   space_add_unique_public_duplicate_skips,
                   space_match_count_calls,
                   space_match_count_key_hits,
                   space_match_count_scan_rows,
                   space_candidate_hits,
                   space_candidate_fallbacks,
                   space_atom_scan_rows,
                   runtime_callable_checks,
                   runtime_callable_cache_hits,
                   runtime_callable_negative_cache_hits,
                   runtime_callable_predicate_hits,
                   runtime_callable_meta_hits,
                   runtime_callable_partial_hits,
                   runtime_noncallable_checks,
                   runtime_noncallable_list_data_hits,
                   runtime_noncallable_obvious_hits,
                   runtime_noncallable_negative_cache_fast_paths,
                   runtime_noncallable_list_data_fast_paths,
                   runtime_noncallable_scalar_fast_paths,
                   runtime_arg_raw_data_fast_paths,
                   var_head_atom_direct_hits,
                   var_head_partial_direct_hits,
                   var_head_direct_fallbacks,
                   unknown_head_negative_cache_fast_paths,
                   partial_plan_cache_hits,
                   partial_plan_cache_stores,
                   partial_direct_compiled_user_hits,
                   partial_direct_runtime_predicate_hits,
                   partial_direct_zero_arg_equation_hits,
                   partial_direct_fallbacks,
                   native_empty_queue_hits,
                   native_enqueue_hits,
                   native_dequeue_hits,
                   native_add_unique_hits,
                   native_range_calls,
                   native_range_hits,
                   native_deep_nest_calls,
                   native_deep_nest_hits,
                   native_fold_nested_sum_calls,
                   native_fold_nested_sum_hits,
                   native_queue_search_calls,
                   native_queue_search_nodes,
                   native_queue_search_neighbor_rows,
                   effect_only_expr_calls,
                   effect_only_fun_direct_hits,
                   effect_only_native_fun_hits,
                   effect_only_native_branching_calls,
                   effect_only_self_add_atom_batches,
                   effect_only_self_add_atom_batch_terms,
                   effect_only_self_add_atom_data_count_batches,
                   effect_only_self_add_atom_data_count_batch_terms
        }
    ' "$log"
done | sort > "$TMP_ROWS"

{
    printf 'case\texit\tcompiled_collections\tcompiled_raw_rows\tcompiled_visible_rows\tcompiled_single_result_calls\tcompiled_single_direct_hits\tcompiled_single_collect_fallbacks\tcompiled_multi_shape_calls\tcompiled_multi_shape_hits\tcompiled_visible_stream_calls\tcompiled_visible_stream_hits\tcompiled_first_visible_calls\tcompiled_first_visible_raw_rows\tcompiled_first_visible_visible_rows\traw_per_collection\tvisible_per_collection\ttyped_calls\ttyped_replays\treplay_rate\tcollect_calls\tcollect_rows\tbind_calls\tbind_rows\tonce_calls\tcount_calls\tcount_rows\tcount_match_fast_hits\tcount_eval_calls\tcount_eval_fast_hits\tcount_eval_range_hits\tcount_eval_mapflat_hits\tfold_calls\tfold_rows\tspace_exact_calls\tspace_exact_hits\tspace_exact_repr_trie_calls\tspace_exact_repr_trie_hits\tspace_add_unique_public_calls\tspace_add_unique_public_added\tspace_add_unique_public_duplicate_skips\tspace_match_count_calls\tspace_match_count_key_hits\tspace_match_count_scan_rows\tspace_candidate_hits\tspace_candidate_fallbacks\tspace_atom_scan_rows\truntime_callable_checks\truntime_callable_cache_hits\truntime_callable_negative_cache_hits\truntime_callable_predicate_hits\truntime_callable_meta_hits\truntime_callable_partial_hits\truntime_noncallable_checks\truntime_noncallable_list_data_hits\truntime_noncallable_obvious_hits\truntime_noncallable_negative_cache_fast_paths\truntime_noncallable_list_data_fast_paths\truntime_noncallable_scalar_fast_paths\truntime_arg_raw_data_fast_paths\tvar_head_atom_direct_hits\tvar_head_partial_direct_hits\tvar_head_direct_fallbacks\tunknown_head_negative_cache_fast_paths\tpartial_plan_cache_hits\tpartial_plan_cache_stores\tpartial_direct_compiled_user_hits\tpartial_direct_runtime_predicate_hits\tpartial_direct_zero_arg_equation_hits\tpartial_direct_fallbacks\tnative_empty_queue_hits\tnative_enqueue_hits\tnative_dequeue_hits\tnative_add_unique_hits\tnative_range_calls\tnative_range_hits\tnative_deep_nest_calls\tnative_deep_nest_hits\tnative_fold_nested_sum_calls\tnative_fold_nested_sum_hits\tnative_queue_search_calls\tnative_queue_search_nodes\tnative_queue_search_neighbor_rows\teffect_only_expr_calls\teffect_only_fun_direct_hits\teffect_only_native_fun_hits\teffect_only_native_branching_calls\teffect_only_self_add_atom_batches\teffect_only_self_add_atom_batch_terms\teffect_only_self_add_atom_data_count_batches\teffect_only_self_add_atom_data_count_batch_terms\n'
    cat "$TMP_ROWS"
} > "$OUT"

printf '%s\n' "$OUT"
