:- dynamic he_auto_typecheck/1.
:- dynamic he_perf_counter/2.
:- dynamic he_perf_counters_enabled/0.
:- dynamic he_stdlib_loaded/0.
:- dynamic installed_surface/2.

profile_feature(he, native_he_core).

:- retractall(he_auto_typecheck(_)),
   assertz(he_auto_typecheck(false)).

he_surface(assertEqual, 2, native(he_native_assert_equal), core).
he_surface(assertAlphaEqual, 2, native(he_native_assert_alpha_equal), core).
he_surface(assert, 1, native(he_native_assert), core).
he_surface(assertEqualToResult, 2, special(assert_equal_to_result), core).
he_surface(assertAlphaEqualToResult, 2, special(assert_alpha_equal_to_result), core).
he_surface(assertEqualMsg, 3, special(assert_equal_msg), compat).
he_surface(assertEqualToResultMsg, 3, special(assert_equal_to_result_msg), compat).
he_surface(assertAlphaEqualMsg, 3, special(assert_alpha_equal_msg), compat).
he_surface(assertAlphaEqualToResultMsg, 3, special(assert_alpha_equal_to_result_msg), compat).
he_surface(assertPeTTaTest, 2, special(assert_petta_test), compat).
he_surface(assertIncludes, 2, special(assert_includes), compat).
he_surface(unify, 4, special(unify), core).
he_surface('add-reduct', 2, special(add_reduct), core).
he_surface(evalc, 2, special(evalc), core).
he_surface(unquote, 1, special(unquote), core).
he_surface('noreduce-eq', 2, special(noreduce_eq), core).
he_surface('if-equal', 4, native(he_native_if_equal), core).
he_surface('if-equal2', 4, native(he_native_if_equal2), core).
he_surface('if-error', 3, native(he_native_if_error), core).
he_surface('return-on-error', 2, native(he_native_return_on_error), core).
he_surface('for-each-in-atom', 2, native(he_native_for_each_in_atom), core).
he_surface('is-function', 1, native(he_native_is_function), core).
he_surface('get-type-space', 2, native(he_native_get_type_space), core).
he_surface('match-types', 4, native(he_native_match_types), core).
he_surface('match-type-or', 3, native(he_native_match_type_or), core).
he_surface('get-doc', 1, native(he_native_get_doc), core).
he_surface('help!', 1, native(he_native_help), core).
he_surface(capture, 1, native(capture), core).
he_surface('format-args', 2, native(he_native_format_args), core).
he_surface('println!', 1, native(he_native_println), core).
he_surface('trace!', 2, native(he_native_trace), core).
he_surface('print-alternatives!', 2, native('print-alternatives!'), extension).
he_surface('_collapse-add-next-atom-from-collapse-bind-result', 2,
           native(he_native_collapse_add_next), compat).
he_surface('unique-atom', 1, native('unique-atom'), compat).
he_surface('union-atom', 2, native('union-atom'), compat).
he_surface('intersection-atom', 2, native('intersection-atom'), compat).
he_surface('subtraction-atom', 2, native('subtraction-atom'), compat).
he_surface('space-len', 1, native('space-len'), extension).
he_surface('space-push', 2, native('space-push'), extension).
he_surface('space-peek', 1, native('space-peek'), extension).
he_surface('space-pop', 1, native('space-pop'), extension).
he_surface('space-get', 2, native('space-get'), extension).
he_surface('space-truncate', 2, native('space-truncate'), extension).
he_surface('add-atoms', 2, native('add-atoms'), extension).
he_surface(quot, 2, native(quot), extension).
he_surface(rem, 2, native(rem), extension).
he_surface(divmod, 2, native(divmod), extension).
he_surface('math.quot', 2, native('math.quot'), extension).
he_surface('math.rem', 2, native('math.rem'), extension).
he_surface('math.mod', 2, native('math.mod'), extension).
he_surface('math.divmod', 2, native('math.divmod'), extension).

he_native_helper(Name, Native) :-
    he_surface(Name, _Arity, native(Native), _Scope).

he_surface_scope(Name, Scope) :-
    he_surface(Name, _Arity, _Kind, Scope).

he_surface_tier(Name, Tier) :-
    he_surface_scope(Name, Tier).

he_native_helper_names(Names) :-
    findall(Name, he_native_helper(Name, _), Raw),
    sort(Raw, Names).

he_compat_helper_signature(Name, OutArity) :-
    he_surface(Name, InArity, _Kind, _Scope),
    OutArity is InArity + 1.

install_profile(he) :-
    !,
    forall(he_surface(Name, InArity, _Kind, _Scope),
           install_surface(he, Name, InArity)),
    ensure_he_stdlib_loaded.
install_profile(_).

install_surface(Profile, Name, InArity) :-
    OutArity is InArity + 1,
    ( installed_surface(Profile, Name/OutArity)
    -> true
    ; register_fun(Name),
      ( arity(Name, OutArity) -> true ; assertz(arity(Name, OutArity)) ),
      assertz(installed_surface(Profile, Name/OutArity))
    ).

ensure_he_stdlib_loaded :-
    he_stdlib_loaded, !.
ensure_he_stdlib_loaded :-
    \+ current_predicate(load_metta_file/2), !.
ensure_he_stdlib_loaded :-
    he_boot_dir(HeDir),
    directory_file_path(HeDir, '..', SrcDir),
    directory_file_path(SrcDir, '..', RootDir),
    directory_file_path(RootDir, 'lib/stdlib.metta', Stdlib),
    load_metta_file(Stdlib, _),
    assertz(he_stdlib_loaded).

he_profile_result(HeOut, _DefaultOut, HeOut) :-
    he_profile_enabled, !.
he_profile_result(_HeOut, DefaultOut, DefaultOut).

he_perf_counters_enable :-
    he_perf_counters_reset,
    ( he_perf_counters_enabled -> true
    ; assertz(he_perf_counters_enabled)
    ).

he_perf_counters_disable :-
    retractall(he_perf_counters_enabled).

he_perf_counters_reset :-
    retractall(he_perf_counter(_, _)).

he_perf_counter_inc(Name) :-
    he_perf_counter_add(Name, 1).

he_perf_counter_add(_Name, Delta) :-
    ( var(Delta)
    ; \+ integer(Delta)
    ; Delta =< 0
    ), !.
he_perf_counter_add(_Name, _Delta) :-
    \+ he_perf_counters_enabled, !.
he_perf_counter_add(Name, Delta) :-
    with_mutex(he_perf_counter,
               ( ( retract(he_perf_counter(Name, Prev))
                 -> Next is Prev + Delta
                 ;  Next = Delta
                 ),
                 assertz(he_perf_counter(Name, Next))
               )).

he_perf_counter_value(Name, Count) :-
    ( he_perf_counter(Name, Count)
    -> true
    ;  Count = 0
    ).

he_perf_counter_snapshot(Pairs) :-
    findall(Count-Name, he_perf_counter(Name, Count), Raw),
    keysort(Raw, Asc),
    reverse(Asc, Desc),
    findall(Name-Count,
            member(Count-Name, Desc),
            Pairs).

he_perf_counters_report(Stream) :-
    format(Stream, 'HE_PERF_COUNTERS_BEGIN~n', []),
    he_perf_counter_snapshot(Pairs),
    forall(member(Name-Count, Pairs),
           format(Stream, '~w\t~w~n', [Name, Count])),
    format(Stream, 'HE_PERF_COUNTERS_END~n', []).
