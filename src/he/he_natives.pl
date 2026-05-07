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

he_native_assert_equal(A, B, []) :- he_assert_set_results([assertEqual, A, B], [A], [B], []).

he_native_assert_alpha_equal(A, B, []) :- he_native_assert_equal(A, B, []).

he_native_assert(_ExprRaw, true, []) :- !.
he_native_assert(_ExprRaw, ['Error'|_]=Error, Error) :- !.
he_native_assert(ExprRaw, _ExprValue, ['Error', [assert, ExprRaw], [ExprRaw, 'not True']]).

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

he_eval_selected_branch(Branch, Out) :-
    ( is_list(Branch)
    -> eval(Branch, Out)
    ;  Out = Branch
    ).

he_native_if_equal(A, B, Then, Else, Out) :-
    he_equal_result(A, B, R),
    ( R == true
    -> he_eval_selected_branch(Then, Out)
    ; R == false
    -> he_eval_selected_branch(Else, Out)
    ; Out = R ).
he_native_if_equal2(A, B, Then, Else, Out) :- he_native_if_equal(A, B, Then, Else, Out).

he_native_if_error(X, A, B, Out) :-
    ( X = ['Error'|_]
    -> he_eval_selected_branch(A, Out)
    ;  he_eval_selected_branch(B, Out)
    ).
he_native_return_on_error(Result, B, Out) :-
    ( Result == 'Empty'
    -> Out = 'Empty'
    ; Result = ['Error'|_]
    -> Out = Result
    ;  he_eval_selected_branch(B, Out)
    ).

he_native_for_each_in_atom(L, F, Out) :- 'map-atom'(L, F, Out).

capture(Expr, Out) :-
    is_list(Expr), !,
    eval(Expr, Out).
capture(Expr, Expr).

he_native_is_function([->|_], true) :- !.
he_native_is_function(_, false).
he_native_get_type_space('&self', X, T) :- !,
    'get-type'(X, T).
he_native_get_type_space(Space0, X, T) :-
    he_resolve_space_ref(Space0, Space),
    catch(match(Space, [':', X, T], T, _), _, fail).
he_native_get_type_space(Space0, X, '%Undefined%') :-
    he_resolve_space_ref(Space0, Space),
    \+ catch(match(Space, [':', X, _], _, _), _, fail).
he_native_match_types(A, B, Then, Else, Out) :-
    he_match_types(A, B, [], Matches),
    ( Matches == [] -> Out = Else ; Out = Then ).
he_native_match_type_or(Value, Type1, Type2, Out) :- he_native_match_types(Type1, Type2, true, Value, Out).
he_native_get_doc(Item, Out) :-
    once('get-doc'(Item, Out)).
he_native_help(Item, Out) :-
    once('help!'(Item, Out)).
he_public_print_text(Arg, Text) :-
    string(Arg), !,
    Text = Arg.
he_public_print_text(Arg, Text) :-
    swrite_public(Arg, Text).
he_native_println(Arg, Out) :-
    he_public_print_text(Arg, Text),
    format('~w~n', [Text]),
    Out = [].
he_native_trace(Arg, Value, Out) :-
    swrite_public(Arg, Text),
    format(user_error, '~s~n', [Text]),
    flush_output(user_error),
    Out = Value.
he_native_collapse_add_next(List, Pair, Out) :-
    ( is_list(List)
    -> true
    ;  Out = ['Error',
              ['_collapse-add-next-atom-from-collapse-bind-result', List, Pair],
              ['BadArgType', 1, 'Expression', 'Atom']],
       !
    ),
    ( Pair = [Value, ['__he_bindings__'|_Bindings]]
    -> append(List, [Value], Out)
    ;  Out = ['Error',
              ['_collapse-add-next-atom-from-collapse-bind-result', List, Pair],
              '(Atom Bindings) pair is expected as a second argument']
    ).
he_native_format_args(Format, Args, Out) :-
    ( string(Format)
    -> true
    ;  Out = ['Error', ['format-args', Format, Args],
              'format-args expects format string as a first argument and expression as a second argument'],
       !
    ),
    ( is_list(Args)
    -> true
    ;  Out = ['Error', ['format-args', Format, Args], 'Atom is not an ExpressionAtom'],
       !
    ),
    maplist(he_format_arg_text, Args, Parts),
    he_format_string(Format, Parts, Out).

he_format_arg_text(Arg, Text) :-
    string(Arg), !,
    Text = Arg.
he_format_arg_text(Arg, Text) :-
    swrite(Arg, Text).

he_format_string(Format, Parts, Out) :-
    ( sub_string(Format, Before, 2, After, "{}")
    -> sub_string(Format, 0, Before, _, Prefix),
       Start is Before + 2,
       sub_string(Format, Start, After, 0, Suffix),
       ( Parts = [Part|Rest]
       -> true
       ;  Part = "",
          Rest = []
       ),
       he_format_string(Suffix, Rest, Tail),
       string_concat(Prefix, Part, PrefixPart),
       string_concat(PrefixPart, Tail, Out)
    ; Out = Format
    ).

he_collect_unique_visible_results(Expr, Results) :-
    once(translate_expr_to_conj(Expr, Conj, Value)),
    findall(Value,
            ( call(Conj),
              he_visible_result(Value)
            ),
            RawResults),
    alpha_list_to_set(RawResults, Results).

he_native_add_reduct(Space, [=, Head, Body], Out) :-
    he_collect_unique_visible_results(Body, BodyReducedList),
    member(BodyReduced0, BodyReducedList),
    % HE add-reduct stores the already-reduced value as the equation body.
    % The singleton wrapper makes the reduced expression a literal body term
    % instead of re-splicing its arguments as a new call.
    'add-atom'(Space, [=, Head, [BodyReduced0]], _),
    Out = [].
he_native_add_reduct(Space, Form, Out) :-
    he_collect_unique_visible_results(Form, ReducedList),
    member(Reduced, ReducedList),
    'add-atom'(Space, Reduced, _),
    Out = [].

he_irreducible_eval_result(In, Goals, Out) :-
    Goals == [],
    copy_term(In-Out, InCopy-OutCopy),
    numbervars(InCopy, 0, _),
    numbervars(OutCopy, 0, _),
    InCopy == OutCopy.

he_alpha_equiv_term(A, B) :-
    copy_term(A-B, ACopy-BCopy),
    numbervars(ACopy, 0, N),
    numbervars(BCopy, N, _),
    ACopy == BCopy.

he_irreducible_eval_keeps_wrapper(Arg) :-
    var(Arg), !.
he_irreducible_eval_keeps_wrapper(Arg) :-
    atom(Arg), !.
he_irreducible_eval_keeps_wrapper(Arg) :-
    is_list(Arg),
    Arg = [Head|_],
    atom(Head).

he_eval_special(Arg, Out) :-
    is_list(Arg),
    Arg = [Fun],
    he_zero_arg_atom_head_body(Fun, Body),
    he_preserve_zero_arg_eval_body(Body), !,
    Out = Body.
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
      ( he_irreducible_eval_keeps_wrapper(Arg),
        he_alpha_equiv_term(Arg, EvalOut)
      -> Out = [eval, Arg]
      ; Out = EvalOut ) ).
