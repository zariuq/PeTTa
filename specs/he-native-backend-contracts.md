# HE Native Backend Contracts

This note records the current intentionally narrow HE-native backend lanes.
These are not broad evaluator shortcuts. Each contract has:

- a recognized translated/runtime shape
- semantic preconditions
- an ordinary fallback path when the shape does not match
- explicit regression coverage

The goal is to keep `--he` fast by routing known safe families to direct
Prolog-level execution while leaving the general HE semantics on the ordinary
path.

## Deterministic compiled call

Recognized shape:
- compiled user/equation calls whose translated/runtime form is known to be a
  direct deterministic result lane

Key code:
- `src/he/he_call.pl`
  - `he_single_result_call_plan/4`
  - `he_call_compiled_equation_or_self/3`
  - `he_build_user_call_native_or_direct_goal/3`

Semantic preconditions:
- the call shape is recognized strongly enough that visible/raw result
  preference is preserved
- multivalue calls stay on the ordinary collector/stream path unless a more
  specific contract says otherwise

Fallback:
- ordinary compiled-equation result selection and visible/raw preference logic

Guard tests:
- `tests/he_compiled_function_multivalue_order.metta`
- `tests/he_once_select_compiled_equation_surface.metta`

## Counted visible match

Recognized shape:
- effect-only prefix followed by an identity-body `match` whose result is only
  consumed by a count/size operation

Key code:
- `src/he/he_answers.pl`
  - `he_effect_only_match_count_body/4`
  - `he_count_visible_results/3`
- `src/he/he_spaces.pl`
  - `he_space_pattern_result_count/3`

Semantic preconditions:
- the prefix is certified effect-only
- the match body is observationally the identity/value-carrying shape expected
  by the counter

Fallback:
- ordinary visible-result enumeration plus counting

Guard tests:
- `tests/he_count_visible_match_surface.metta`
- `tests/he_match_identity_body_surface.metta`

## Count-eval

Recognized shape:
- `size-atom(eval(...))`
- `length(eval(...))`
- specific `let` / `chain` wrappers where the bound value is only consumed by
  one of those count-like consumers
- currently fastable families are `[]`, `range`, and specific
  `map-flat(range(...))` lanes

Key code:
- `src/he/he_answers.pl`
  - `he_count_eval_expr/2`
  - `he_count_eval_expr_fast/2`
- `src/he/he_translator.pl`
  - named count-eval detectors used by `he_translate_special/5`

Semantic preconditions:
- the producer expression is one of the recognized count-preserving families
- no intermediate consumer requires the actual materialized list

Fallback:
- ordinary `eval` then `size-atom` / `length`

Guard tests:
- `tests/he_count_eval_expr_surface.metta`
- `tests/profile_repros/he_holbenchmark_mapflat_range_measure.metta`

## Effect-only branching

Recognized shape:
- unused `let` / `chain` bindings whose value side is proven effect-only
- recursive effect-only branching families with data-only `&self` insertion

Key code:
- `src/he/he_call.pl`
  - `he_effect_only_safe_root_expr/1`
  - `he_effect_only_expr/1`
  - `he_effect_only_native_plan/3`
  - `he_effect_only_native_call/2`

Semantic preconditions:
- the unused binding is truly unused in the continuation
- the effect-only proof excludes multiplicity-sensitive consumers
- batched `&self` insertion remains plain-data only

Fallback:
- ordinary translated `let` / `chain` evaluation

Guard tests:
- `tests/he_unused_binding_effect_only_recursive_surface.metta`
- `tests/he_unused_binding_multivalue_preserves_multiplicity.metta`
- `tests/he_unused_binding_recursive_multivalue_arg_preserves_multiplicity.metta`

## Ground recursive memo

Recognized shape:
- deterministic compiled user/equation calls with ground arguments
- recursive bodies that call the same function from multiple branches

Key code:
- `src/he/he_call.pl`
  - `he_single_result_recursive_fun/2`
  - `he_single_result_ground_memo_candidate/2`
  - `he_single_result_ground_memo_store/3`
  - `he_expr_call_count/3`

Semantic preconditions:
- the single-result call plan is already safe
- arguments are ground
- the produced result is ground, non-empty, and not an error
- equation/function metadata mutation invalidates the memo cache

Fallback:
- ordinary deterministic compiled call selection

Guard tests:
- `tests/he_ground_recursive_memo_surface.metta`

## Numeric recursion contract

Recognized shape:
- two-argument trial-divisor recursion:
  - stop when `D * D > N`
  - return `D` when `N % D == 0`
  - otherwise recurse with `D + 1`

Key code:
- `src/he/he_call.pl`
  - `he_native_contract_plan/3`
  - `he_trial_divisor_native_fun/1`
  - `he_native_trial_divisor_call/4`

Semantic preconditions:
- the translated function body exactly matches the recognized recursive shape
- runtime arguments reduce to positive integer divisor state
- nonmatching runtime calls fall back to the ordinary data-shaped result

Fallback:
- ordinary compiled recursion

Guard tests:
- `tests/he_eq_callable_prime.metta`
- `tests/profile_repros/he_prime_find_divisor_single.metta`
- full translator survey row `examples/superpose_primes.metta`

## Indexed count contract

Recognized shape:
- a recursive `add-atom` producer over one relation and modulus
- a wrapper that immediately queries total, first-key, second-key,
  relation-name, and full-pair counts

Key code:
- `src/he/he_call.pl`
  - `he_self_add_desc_mod_contract/3`
  - `he_indexing_demo_contract/10`
  - `he_native_indexing_demo_call/11`

Semantic preconditions:
- the producer relation and modulus are recovered from the exact body shape
- query helpers are collapse/match identity functions over the same relation
- the native path inserts the same public facts before returning counts

Fallback:
- ordinary translated recursion and match/count evaluation

Guard tests:
- `tests/he_scale_indexing_contract_surface.metta`

## Queue-search contract

Recognized shape:
- translated search wrappers lowered to
  `queue_search_contract(Space, SeedMode, StatePlan, NeighborPlan)`

Current intentionally narrow family:
- `StatePlan = board9`
- `NeighborPlan = move9_stream`

Key code:
- `src/he/he_call.pl`
  - `he_unique_queue_search_plan/3`
  - `he_unique_queue_search_plan_1/3`
  - `he_native_unique_queue_search_call/3`
  - `he_native_unique_queue_search_limited_call/4`

Semantic preconditions:
- queue structure matches the recognized wrapper
- seeded vs unseeded uniqueness semantics are preserved
- state validation and neighbor generation match the explicit plan

Fallback:
- ordinary compiled recursion / queue operations

Guard tests:
- `tests/he_bfs_all_wrapper_surface.metta`
- `tests/he_bfs_all_limited_wrapper_surface.metta`
- `tests/he_move9_native_surface.metta`
- `tests/profile_repros/he_tilepuzzle_imported_bfs_500_witness.metta`

## Exact repr membership and unique add

Recognized shape:
- uniqueness checks through explicit repr-backed membership and public unique
  add semantics

Key code:
- `src/he/he_spaces.pl`
  - `he_space_add_unique_public/4`
  - `he_space_exact_member/2`
- `src/he/he_answers.pl`
  - unique-space fold helpers

Semantic preconditions:
- public value is converted through the ordinary repr path
- mutation result still flows through the public `add-atom` semantics

Fallback:
- ordinary atomspace mutation and visibility behavior

Guard tests:
- `tests/he_space_exact_repr_surface.metta`
- `tests/he_unique_space_fold_surface.metta`

## Notes

- Visible/raw answer preference and typed replay policy now live in
  `src/he/he_answers.pl`, even when the call substrate itself is owned by
  `src/he/he_call.pl`. This keeps result-policy decisions separate from call
  routing.
- These contracts should remain narrow until a second real workload justifies
  widening them.
- New contracts should be introduced by named detectors and explicit fallback,
  not by broad evaluator heuristics.
