:- meta_predicate he_collect_assert_eval_actual(?, 0, ?, ?).

he_result_key(Term, Key) :-
    he_public_result(Term, Public),
    copy_term(Public, Copy),
    he_normalize_state_term(Copy, Norm),
    numbervars(Norm, 0, _),
    swrite(Norm, Key).

he_public_result(Term, Public) :-
    cyclic_term(Term), !,
    Public = Term.
he_public_result([quote, Term], Public) :-
    !,
    he_public_syntax_result(Term, Public).
he_public_result(Term, Public) :-
    nonvar(Term),
    Term = partial(Fun, Args), !,
    he_public_result_list(Args, PublicArgs),
    Public = [Fun|PublicArgs].
he_public_result(Term, Public) :-
    is_list(Term), !,
    he_public_result_list(Term, Public).
he_public_result(Term, Term).

he_public_syntax_result(Term, Public) :-
    ( var(Term)
    ; atomic(Term)
    ), !,
    Public = Term.
he_public_syntax_result(Term, Public) :-
    is_list(Term), !,
    maplist(he_public_syntax_result, Term, Public).
he_public_syntax_result(Term, Public) :-
    Term =.. [F|Args],
    maplist(he_public_syntax_result, Args, PublicArgs),
    Public =.. [F|PublicArgs].

he_public_result_list([], []).
he_public_result_list([Term|Terms], [Public|Publics]) :-
    he_public_result(Term, Public),
    he_public_result_list(Terms, Publics).

he_same_results(Actuals, Expecteds) :-
    maplist(he_result_key, Actuals, ActualKeys),
    maplist(he_result_key, Expecteds, ExpectedKeys),
    msort(ActualKeys, ActualSorted),
    msort(ExpectedKeys, ExpectedSorted),
    ActualSorted == ExpectedSorted.

he_same_result_set(Actuals, Expecteds) :-
    maplist(he_result_key, Actuals, ActualKeys),
    maplist(he_result_key, Expecteds, ExpectedKeys),
    sort(ActualKeys, ActualSorted),
    sort(ExpectedKeys, ExpectedSorted),
    ActualSorted == ExpectedSorted.

he_assert_same_results(Label, Actuals, Expecteds, []) :-
    ( he_same_results(Actuals, Expecteds) -> true
    ; swrite(Label, RLabel),
      swrite(Actuals, RActuals),
      swrite(Expecteds, RExpecteds),
      format("Assertion failed: ~w~nExpected results: ~w~nActual results: ~w~n",
             [RLabel, RExpecteds, RActuals]),
      halt(1) ).

he_assert_set_results(Label, Actuals, Expecteds, []) :-
    ( he_same_result_set(Actuals, Expecteds) -> true
    ; swrite(Label, RLabel),
      swrite(Actuals, RActuals),
      swrite(Expecteds, RExpecteds),
      format("Assertion failed: ~w~nExpected results: ~w~nActual results: ~w~n",
             [RLabel, RExpecteds, RActuals]),
      halt(1) ).

he_collect_source_test_actual(ExprConj, ExprVal, Actual) :-
    he_collect_visible_results(ExprConj, ExprVal, Results),
    ( Results = [Only]
    -> Actual = Only
    ;  Actual = Results
    ).

he_assert_equal_to_eval(Label, Actual, Expected, true) :-
    ( he_assert_eval_matches(Actual, Expected)
    -> true
    ; swrite(Label, RLabel),
      he_public_result(Actual, PublicActual),
      he_public_result(Expected, PublicExpected),
      swrite(PublicActual, RActual),
      swrite(PublicExpected, RExpected),
      format("Assertion failed: ~w~nExpected: ~w~nActual: ~w~n",
             [RLabel, RExpected, RActual]),
      halt(1)
    ).

he_assert_eval_matches(Actual, Expected) :-
    var(Expected), !,
    Expected = Actual.
he_assert_eval_matches(Actual, Expected) :-
    he_result_key(Actual, ActualKey),
    he_result_key(Expected, ExpectedKey),
    ActualKey == ExpectedKey.

he_collect_assert_eval_actual(ExprVal, ExprConj, Expected, Actual) :-
    findnsols(2, ExprVal, ExprConj, Sampled),
    ( Sampled = [First|_],
      he_assert_eval_matches(First, Expected)
    -> Actual = First
    ; Sampled = [Actual]
    -> true
    ; findall(ExprVal, ExprConj, Results),
      ( Results = [First|_],
        he_assert_eval_matches(First, Expected)
      -> Actual = First
      ; Results = [Actual]
      -> true
      ; Actual = Results
      )
    ).

he_assert_same_results_or_error(Subject, Actuals, Expecteds, Msg, Out) :-
    ( he_same_results(Actuals, Expecteds)
    -> Out = []
    ;  Out = ['Error', Subject, Msg]
    ).

he_collect_assert_result_sets(ExprConj, ExprVal, ExpConj, ExpVal, Actuals, Expecteds) :-
    he_collect_visible_results(ExprConj, ExprVal, Actuals),
    he_collect_visible_results(ExpConj, ExpVal, Expecteds).

he_collect_assert_result_set_or_singleton(ExprConj, ExprVal, ExpConj, ExpVal, Actuals, Expecteds) :-
    he_collect_visible_results(ExprConj, ExprVal, Actuals),
    he_collect_visible_results(ExpConj, ExpVal, Expecteds0),
    ( Expecteds0 == []
    -> Expecteds = [ExpVal]
    ;  Expecteds = Expecteds0
    ).

he_collect_assert_result_tuple(ExprConj, ExprVal, ExpectedTuple, Actuals, Expecteds) :-
    he_collect_visible_results(ExprConj, ExprVal, Actuals),
    he_expected_tuple_results(ExpectedTuple, Expecteds).

he_assert_set_results_or_error(Subject, Actuals, Expecteds, Msg, Out) :-
    ( he_same_result_set(Actuals, Expecteds)
    -> Out = []
    ;  Out = ['Error', Subject, Msg]
    ).

he_expected_tuple_results(Results, Results) :-
    is_list(Results), !.
he_expected_tuple_results(Result, [Result]).

he_assert_includes_expected_key(Expected, ActualKeys) :-
    he_result_key(Expected, ExpectedKey),
    memberchk(ExpectedKey, ActualKeys).

he_assert_includes_results(_Subject, Actuals, Expecteds, []) :-
    maplist(he_result_key, Actuals, ActualKeys),
    forall(member(Expected, Expecteds),
           he_assert_includes_expected_key(Expected, ActualKeys)),
    !.
he_assert_includes_results(Subject, Actuals, Expecteds, ['Error', Subject, Msg]) :-
    he_public_result_list(Expecteds, PublicExpecteds),
    he_public_result_list(Actuals, PublicActuals),
    Msg = [assertIncludes, 'error:', PublicExpecteds, not, included, in, 'result:', PublicActuals].
