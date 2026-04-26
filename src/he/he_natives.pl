he_profile_eq(A, B, R) :-
    he_profile_enabled, !,
    he_eval_if_expr(A, EA),
    he_eval_if_expr(B, EB),
    ( EA = ['Error'|_] -> R = EA
    ; EB = ['Error'|_] -> R = EB
    ; EA =@= EB -> R = true
    ; R = false ).

he_profile_ne(A, B, R) :-
    he_profile_enabled, !,
    he_eval_if_expr(A, EA),
    he_eval_if_expr(B, EB),
    ( EA = ['Error'|_] -> R = EA
    ; EB = ['Error'|_] -> R = EB
    ; EA =@= EB -> R = false
    ; R = true ).

he_native_assert_equal(A, B, true) :- he_assert_set_results([assertEqual, A, B], [A], [B], true).

he_native_assert_alpha_equal(A, B, true) :- he_native_assert_equal(A, B, true).

he_equal_result(A, B, true) :-
    he_eval_if_expr(A, EA),
    he_eval_if_expr(B, EB),
    \+ (EA = ['Error'|_]),
    \+ (EB = ['Error'|_]),
    EA =@= EB, !.
he_equal_result(A, _, Error) :-
    he_eval_if_expr(A, EA),
    EA = ['Error'|_], !,
    Error = EA.
he_equal_result(_, B, Error) :-
    he_eval_if_expr(B, EB),
    EB = ['Error'|_], !,
    Error = EB.
he_equal_result(_, _, false).

he_native_if_equal(A, B, Then, Else, Out) :-
    he_equal_result(A, B, R),
    ( R == true
    -> Out = Then
    ; R == false
    -> Out = Else
    ; Out = R ).
he_native_if_equal2(A, B, Then, Else, Out) :- he_native_if_equal(A, B, Then, Else, Out).

he_native_if_error(X, A, B, Out) :- ( X = ['Error'|_] -> Out = A ; Out = B ).
he_native_return_on_error(Result, B, Out) :- he_native_if_error(Result, Result, B, Out).

he_native_for_each_in_atom(L, F, Out) :- 'map-atom'(L, F, Out).

he_native_is_function([->|_], true) :- !.
he_native_is_function(_, false).
he_native_get_type_space('&self', X, T) :- 'get-type'(X, T).
he_native_match_types(A, B, Then, Else, Out) :-
    he_match_types(A, B, [], Matches),
    ( Matches == [] -> Out = Else ; Out = Then ).
he_native_match_type_or(Value, Type1, Type2, Out) :- he_native_match_types(Type1, Type2, true, Value, Out).

he_native_add_reduct(Space, [=, Head, Body], true) :-
    eval(Body, BodyReduced),
    % HE add-reduct stores the already-reduced value as the equation body.
    % The singleton wrapper makes the reduced expression a literal body term
    % instead of re-splicing its arguments as a new call.
    'add-atom'(Space, [=, Head, [BodyReduced]], _).

he_irreducible_eval_result(In, Goals, Out) :-
    Goals == [],
    copy_term(In-Out, InCopy-OutCopy),
    numbervars(InCopy, 0, _),
    numbervars(OutCopy, 0, _),
    InCopy == OutCopy.

he_irreducible_eval_keeps_wrapper(Arg) :-
    var(Arg), !.
he_irreducible_eval_keeps_wrapper(Arg) :-
    atom(Arg), !.
he_irreducible_eval_keeps_wrapper(Arg) :-
    is_list(Arg),
    Arg = [Head|_],
    atom(Head).

he_eval_special(Arg, Out) :-
    nonvar(Arg),
    Arg = ['Error'|_], !,
    Out = Arg.
he_eval_special(Arg, Out) :-
    once(translate_expr(Arg, Goals, EvalOut)),
    ( he_irreducible_eval_result(Arg, Goals, EvalOut),
      he_irreducible_eval_keeps_wrapper(Arg)
    -> Out = [eval, Arg]
    ; call_goals(Goals),
      Out = EvalOut ).
