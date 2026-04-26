# HE Runtime Profiling After Shared Fast Paths (2026-04-25)

This note records the first post-fix profiling rerun after:

1. caching `he_function_typechain/2` / `he_function_typechains/2`
2. invalidating that cache on `:` fact add/remove
3. fast-pathing `he_resolve_space_ref('&self', '&self')`
4. skipping the generic HE match override for common non-state `&self` matches

Command:

```bash
cd /home/zar/claude/tmp/petta-he-profile
ulimit -v 10485760
TIMEOUT_SECONDS=12 TOP=20 tests/tools/profile_he_remaining.sh
```

## Headline

The shared runtime hotspot shape changed materially for `pln_roman` and
`nars_tuffy`.

What fell out of the top profile:

- `he_bridge_match_override/4`
- `he_match_state_semantic/4`
- `he_term_has_state/1` (for the PLN/NARS lanes)
- `nb_getval/2`

What replaced it:

- `he_direct_space_match/4`
- `he_fast_plain_self_matchable/1`
- `he_plain_term_without_state_ref/1`
- cache hits in `he_function_typechains_cache/2`

So the work did what it was supposed to do: the HE runtime is no longer paying
the full state-semantics / generic-override tax for the common plain `&self`
match cases in the query-heavy examples.

## Per-case read

### pln_roman

Before:

- `match/4` ~70% inclusive child time
- `he_bridge_match_override/4`, `he_match_state_semantic/4`,
  `he_function_typechain/2`, `nb_getval/2`, `he_term_has_state/1` all hot

After:

- `match/4` ~48% inclusive child time
- `he_direct_space_match/4` now explicit in the top set
- `he_function_typechains/2` + `he_function_typechains_cache/2` show cache use
- `he_bridge_match_override/4` and `he_match_state_semantic/4` are gone
- `he_term_has_state/1` and `nb_getval/2` are gone from the top set

Interpretation:

- The shared HE fast path is working.
- The remaining cost is now the cheaper syntactic plain-match screening path
  plus direct dynamic lookup / type work, not the full state-aware override path.

### nars_tuffy

Before:

- Same family as `pln_roman`
- `match/4` ~72% inclusive child time
- state-override / metadata churn dominated

After:

- `match/4` ~48% inclusive child time
- `he_direct_space_match/4` is the new explicit self-match cost center
- `he_function_typechains_cache/2` is active
- `he_bridge_match_override/4`, `he_match_state_semantic/4`,
  `he_term_has_state/1`, and `nb_getval/2` are no longer leading hotspots

Interpretation:

- Same story as `pln_roman`: the generic HE override tax was reduced
  substantially, and the remaining wall is now in cheaper direct-match and type
  plumbing.

### tilepuzzle

No meaningful change in family.

Still dominated by:

- `current_predicate/1`
- `clause/2`
- `he_term_has_state/1`
- `term_to_atom/2`
- dynamic space scans in the translated functional queue / dedup path

Interpretation:

- The shared HE fast path does not address the tile/search workload much.
- This still points toward a separate queue/hash / search-surface optimization
  tranche.

### hyperpose_primes

Still not honestly characterized by plain `profile/1`.

Top profile remains:

- `thread_create/3`
- autoload / setup

Interpretation:

- Need thread-aware profiling or direct instrumentation around the worker path.

## Next specialization choice

Best next shared step:

1. reduce the new plain `&self` screening tax
   (`he_fast_plain_self_matchable/1`, `he_plain_term_without_state_ref/1`,
   `atom_concat/3`, repeated `he_profile_enabled/0`)

Then:

2. attack the separate tile/search family
3. do thread-aware `hyperpose` profiling
