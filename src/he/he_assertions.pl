:- meta_predicate he_collect_petta_test_actual(?, 0, ?, ?).

he_result_key(Term, Key) :-
    copy_term(Term, Copy),
    he_normalize_state_term(Copy, Norm),
    numbervars(Norm, 0, _),
    swrite(Norm, Key).

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

he_assert_same_results(Label, Actuals, Expecteds, true) :-
    ( he_same_results(Actuals, Expecteds) -> true
    ; swrite(Label, RLabel),
      swrite(Actuals, RActuals),
      swrite(Expecteds, RExpecteds),
      format("Assertion failed: ~w~nExpected results: ~w~nActual results: ~w~n",
             [RLabel, RExpecteds, RActuals]),
      halt(1) ).

he_assert_set_results(Label, Actuals, Expecteds, true) :-
    ( he_same_result_set(Actuals, Expecteds) -> true
    ; swrite(Label, RLabel),
      swrite(Actuals, RActuals),
      swrite(Expecteds, RExpecteds),
      format("Assertion failed: ~w~nExpected results: ~w~nActual results: ~w~n",
             [RLabel, RExpecteds, RActuals]),
      halt(1) ).

he_petta_test_matches(Actual, Expected) :-
    var(Expected), !,
    Expected = Actual.
he_petta_test_matches(Actual, Expected) :-
    he_result_key(Actual, ActualKey),
    he_result_key(Expected, ExpectedKey),
    ActualKey == ExpectedKey.

he_collect_petta_test_actual(ExprVal, ExprConj, Expected, Actual) :-
    findnsols(2, ExprVal, ExprConj, Sampled),
    ( Sampled = [First|_],
      he_petta_test_matches(First, Expected)
    -> Actual = First
    ; Sampled = [Actual]
    -> true
    ; findall(ExprVal, ExprConj, Results),
      ( Results = [First|_],
        he_petta_test_matches(First, Expected)
      -> Actual = First
      ; Results = [Actual]
      -> true
      ; Actual = Results
      )
    ).

he_assert_petta_test(Label, Actual, Expected, true) :-
    ( he_petta_test_matches(Actual, Expected)
    -> true
    ; swrite(Label, RLabel),
      swrite(Actual, RActual),
      swrite(Expected, RExpected),
      format("Assertion failed: ~w~nExpected: ~w~nActual: ~w~n",
             [RLabel, RExpected, RActual]),
      halt(1) ).

he_expected_tuple_results(Results, Results) :-
    is_list(Results), !.
he_expected_tuple_results(Result, [Result]).
