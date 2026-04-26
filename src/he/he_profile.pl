:- dynamic he_auto_typecheck/1.
:- dynamic installed_surface/2.

profile_feature(he, native_he_core).

:- retractall(he_auto_typecheck(_)),
   assertz(he_auto_typecheck(false)).

he_surface(assertEqual, 2, native(he_native_assert_equal), core).
he_surface(assertAlphaEqual, 2, native(he_native_assert_alpha_equal), core).
he_surface(assertEqualToResult, 2, special(assert_equal_to_result), core).
he_surface(assertAlphaEqualToResult, 2, special(assert_alpha_equal_to_result), core).
he_surface(assertPeTTaTest, 2, special(assert_petta_test), compat).
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
           install_surface(he, Name, InArity)).
install_profile(_).

install_surface(Profile, Name, InArity) :-
    OutArity is InArity + 1,
    ( installed_surface(Profile, Name/OutArity)
    -> true
    ; register_fun(Name),
      ( arity(Name, OutArity) -> true ; assertz(arity(Name, OutArity)) ),
      assertz(installed_surface(Profile, Name/OutArity))
    ).

he_profile_result(HeOut, _DefaultOut, HeOut) :-
    he_profile_enabled, !.
he_profile_result(_HeOut, DefaultOut, DefaultOut).
