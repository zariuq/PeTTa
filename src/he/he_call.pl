he_user_functor_prefix('$metta$:').

:- multifile he_clause_functor/2.
:- dynamic he_compiled_goal_resolution/3.
:- dynamic he_compiled_goal_no_resolution/2.
:- dynamic he_runtime_callable_head_cache/1.
:- dynamic he_call_partial_arity_cache/3.

metta_user_functor(Fun, UserFun) :-
    atom(Fun),
    he_user_functor_prefix(Prefix),
    atom_concat(Prefix, Fun, UserFun).

he_clause_functor(Fun, Fun) :-
    \+ he_profile_enabled, !.
he_clause_functor(Fun, UserFun) :-
    metta_user_functor(Fun, UserFun).

he_returns_self_on_failure(eval) :-
    he_profile_enabled, !.
he_returns_self_on_failure(Fun) :-
    he_profile_enabled,
    he_constructor_symbol(Fun), !.
he_returns_self_on_failure(Fun) :-
    he_has_atom_head_equation(Fun), !.
he_returns_self_on_failure(Fun) :-
    catch(nb_getval(Fun, Metas), _, fail),
    is_list(Metas),
    Metas \= [], !.

he_constructor_symbol(Fun) :-
    atom(Fun),
    atom_chars(Fun, [First|_]),
    char_type(First, upper).

he_unify_success(Space, Pattern) :-
    he_space_ref_atom(Space), !,
    once(match(Space, Pattern, Pattern, _)).
he_unify_success(A, B) :- A = B.

he_call_typed(Fun, Args, TypeChains, Out) :-
    he_fast_typed_call(Fun, Args, TypeChains, Out), !.
he_call_typed(Fun, Args, TypeChains, Out) :-
    he_maybe_register_specialization_types(Fun, Args, TypeChains),
    he_display_call_args(Fun, Args, DisplayArgs),
    include(he_typechain_arity_matches(Args), TypeChains, MatchingArity),
    ( MatchingArity == []
    -> Out = ['Error', [Fun|DisplayArgs], 'IncorrectNumberOfArguments']
    ; he_first_error_arg(Args, ExistingError)
    -> Out = ExistingError
    ; ( he_typed_call_has_selection(Fun, Args, DisplayArgs, MatchingArity)
      -> he_typed_call_selection_result(Fun, Args, DisplayArgs, MatchingArity, Out)
      ;  Out = [Fun|Args]
      )
    ).

he_typed_call_has_selection(Fun, Args, DisplayArgs, TypeChains) :-
    he_select_typed_call([Fun|DisplayArgs], TypeChains, Args, _), !.

he_typed_call_selection_result(Fun, Args, DisplayArgs, TypeChains, Out) :-
    findall(Selection,
            he_select_typed_call([Fun|DisplayArgs], TypeChains, Args, Selection),
            Selections0),
    sort(Selections0, Selections),
    Selections \= [],
    he_finish_typed_call_selections(Fun, Args, DisplayArgs, Selections, Out).

he_select_typed_call(Call, [TypeChain|_], _Args, ok(TypeChain, ReturnType)) :-
    he_typechain_return_type(TypeChain, ReturnType),
    he_check_if_function_type_is_applicable(Call, TypeChain, '%Undefined%', '&self', [], Check),
    Check = ok(_).
he_select_typed_call(Call, [_|Rest], Args, Selection) :-
    he_select_typed_call(Call, Rest, Args, Selection).
he_select_typed_call(Call, TypeChains, Args, err(TypeChain, Errors, Args)) :-
    \+ ( member(OkTypeChain, TypeChains),
         he_check_if_function_type_is_applicable(Call, OkTypeChain, '%Undefined%', '&self', [], ok(_))
       ),
    member(TypeChain, TypeChains),
    he_check_if_function_type_is_applicable(Call, TypeChain, '%Undefined%', '&self', [], err(Errors)), !.

he_typechain_return_type([->|TypeItems], ReturnType) :-
    append(_, [ReturnType], TypeItems).

he_finish_typed_call_selections('get-type', Args, DisplayArgs, Selections, Out) :-
    !,
    findall(Candidate,
            ( catch(he_invoke_typed('get-type', Args, Raw0), _, fail),
              member(ok(_, ReturnType), Selections),
              he_cast_typed_raw_result('get-type', Args, DisplayArgs, ReturnType, Raw0, Candidate)
            ),
            Candidates0),
    alpha_list_to_set(Candidates0, Candidates),
    member(Out, Candidates).
he_finish_typed_call_selections(Fun, Args, DisplayArgs, Selections, Out) :-
    he_collect_typed_nonerror_solutions(Fun, Args, DisplayArgs, Selections, Solutions),
    Solutions \= [],
    !,
    member(BoundArgs-Out, Solutions),
    Args = BoundArgs.
he_finish_typed_call_selections(Fun, Args, DisplayArgs, Selections, Out) :-
    member(Selection, Selections),
    he_finish_typed_call(Fun, Args, DisplayArgs, Selection, Out), !.

he_collect_typed_nonerror_solutions(Fun, Args, DisplayArgs, Selections, Solutions) :-
    findall(BoundArgs-Candidate,
            he_typed_nonerror_solution(Fun, Args, DisplayArgs, Selections, BoundArgs, Candidate),
            Solutions0),
    alpha_list_to_set(Solutions0, Solutions).

he_typed_nonerror_solution(Fun, Args, DisplayArgs, Selections, BoundArgs, Candidate) :-
    copy_term(Args-DisplayArgs, ArgsCopy-DisplayCopy),
    member(ok(TypeChain, ReturnType), Selections),
    TypeChain = [->|_],
    catch(he_invoke_typed(Fun, ArgsCopy, Raw0), _, fail),
    he_cast_typed_raw_result(Fun, ArgsCopy, DisplayCopy, ReturnType, Raw0, Candidate),
    \+ he_error_atom(Candidate),
    BoundArgs = ArgsCopy.

he_cast_typed_raw_result(Fun, Args, DisplayArgs, ReturnType, Raw0, Out) :-
    he_maybe_eval_typed_return(ReturnType, Raw0, RawOut),
    ( Fun == 'get-type'
    -> Out = RawOut
    ; RawOut = [Fun|Args]
    -> Out = RawOut
    ; he_cast_result([Fun|DisplayArgs], ReturnType, RawOut, Out)
    ).

he_finish_typed_call(Fun, Args, DisplayArgs, ok(TypeChain, ReturnType), Out) :-
    TypeChain = [->|_],
    catch(he_invoke_typed(Fun, Args, Raw0), _, fail),
    he_maybe_eval_typed_return(ReturnType, Raw0, RawOut),
    ( Fun == 'get-type'
    -> Out = RawOut
    ; RawOut = [Fun|Args]
    -> Out = RawOut
    ; he_cast_result([Fun|DisplayArgs], ReturnType, RawOut, Out)
    ).
he_finish_typed_call(Fun, Args, _DisplayArgs, ok(TypeChain, _ReturnType), Out) :-
    TypeChain = [->|TypeItems],
    append(ArgTypes, [_], TypeItems),
    ( Fun == 'get-type'
    -> fail
    ; he_args_have_undefined(Args, ArgTypes)
    -> Out = [Fun|Args]
    ; he_args_include_data_type(ArgTypes)
    -> Out = [Fun|Args]
    ; he_static_callable_for_args(Fun, Args)
    -> fail
    ; he_eval_constructor_args(Args, EvalArgs),
      Out = [Fun|EvalArgs]
    ).
he_finish_typed_call(_Fun, _Args, _DisplayArgs, err(_TypeChain, [Error|_], _), Error).
he_finish_typed_call(Fun, Args, _DisplayArgs, err(_TypeChain, [], _), [Fun|Args]).

he_fast_typed_call('+', [A, B], _, R) :-
    number(A), number(B), !,
    R is A + B.
he_fast_typed_call('-', [A, B], _, R) :-
    number(A), number(B), !,
    R is A - B.
he_fast_typed_call('*', [A, B], _, R) :-
    number(A), number(B), !,
    R is A * B.
he_fast_typed_call('/', [A, B], _, R) :-
    number(A), number(B), !,
    R is A / B.
he_fast_typed_call('%', [A, B], _, R) :-
    integer(A), integer(B), !,
    R is A mod B.
he_fast_typed_call('<', [A, B], _, R) :-
    number(A), number(B), !,
    ( A < B -> R = true ; R = false ).
he_fast_typed_call('>', [A, B], _, R) :-
    number(A), number(B), !,
    ( A > B -> R = true ; R = false ).
he_fast_typed_call('<=', [A, B], _, R) :-
    number(A), number(B), !,
    ( A =< B -> R = true ; R = false ).
he_fast_typed_call('>=', [A, B], _, R) :-
    number(A), number(B), !,
    ( A >= B -> R = true ; R = false ).
he_fast_typed_call('==', [A, B], _, R) :-
    he_fast_typed_literal(A),
    he_fast_typed_literal(B), !,
    ( A =@= B -> R = true ; R = false ).
he_fast_typed_call('!=', [A, B], _, R) :-
    he_fast_typed_literal(A),
    he_fast_typed_literal(B), !,
    ( A =@= B -> R = false ; R = true ).

he_fast_typed_literal(A) :-
    number(A), !.
he_fast_typed_literal(A) :-
    string(A), !.
he_fast_typed_literal(true) :- !.
he_fast_typed_literal(false) :- !.
he_fast_typed_literal('True') :- !.
he_fast_typed_literal('False') :- !.
he_fast_typed_literal(A) :-
    atom(A),
    \+ fun(A).

he_display_call_args('change-state!', [State|Rest], [DisplayState|Rest]) :-
    he_state_handle(State, Id),
    state_cell(Id, _, InitValue), !,
    DisplayState = ['new-state', InitValue].
he_display_call_args(_, Args, Args).

he_eval_constructor_args([], []).
he_eval_constructor_args([Arg|Args], [Eval|Rest]) :-
    he_eval_constructor_arg(Arg, Eval),
    he_eval_constructor_args(Args, Rest).

he_eval_constructor_arg(Arg, Eval) :-
    is_list(Arg),
    Arg = [Head|_],
    \+ ( atom(Head), \+ fun(Head) ),
    catch(eval(Arg, Eval0), _, fail), !,
    Eval = Eval0.
he_eval_constructor_arg(Arg, Arg).

he_eval_return_if_callable(In, Out) :-
    is_list(In),
    In = [Head|_],
    atom(Head),
    fun(Head), !,
    ( catch(eval(In, EvalOut), _, fail)
    -> Out = EvalOut
    ; Out = In ).
he_eval_return_if_callable(In, In).

he_maybe_eval_typed_return(ReturnType, In, Out) :-
    nonvar(ReturnType),
    ReturnType == '%Undefined%', !,
    he_eval_return_if_callable(In, Out).
he_maybe_eval_typed_return(_, In, In).

he_has_atom_head_equation(Fun) :-
    atom(Fun),
    he_eq_fact(Fun, _, _, _).

he_invoke_typed(Fun, Args, RawOut) :-
    he_profile_enabled,
    he_compiled_user_goal([Fun|Args], RawOut, Goal), !,
    catch(call(Goal), _, fail).
he_invoke_typed(Fun, Args, RawOut) :-
    he_profile_enabled,
    he_has_atom_head_equation(Fun), !,
    append(Args, [RawOut], CallArgs),
    Goal =.. [Fun|CallArgs],
    catch(call(Goal), _, fail).
he_invoke_typed(Fun, Args, RawOut) :-
    append(Args, [RawOut], CallArgs),
    Goal =.. [Fun|CallArgs],
    call(Goal).

he_static_callable_for_args(Fun, Args) :-
    he_profile_enabled,
    he_compiled_user_goal([Fun|Args], _Out, _Goal), !.
he_static_callable_for_args(Fun, _Args) :-
    he_profile_enabled,
    he_has_atom_head_equation(Fun), !.
he_static_callable_for_args(Fun, Args) :-
    append(Args, [_], CallArgs),
    length(CallArgs, Arity),
    current_predicate(Fun/Arity),
    \+ (current_op(_, _, Fun), Arity =< 2).

he_call_has_equation(Call) :-
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_eq_fact(Fun, Arity, HeadArgs, _),
    HeadArgs = Args, !.
he_call_has_equation(Call) :-
    copy_term(Call, CallCopy),
    catch(match('&self', [=, CallCopy, Body], Body, _), _, fail), !.

he_call_has_fun_meta([Fun|Args]) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta(HeadArgs, _), Metas),
    copy_term(HeadArgs-Args, HeadCopy-ArgsCopy),
    HeadCopy = ArgsCopy, !.

he_invalidate_compiled_goal_resolution(Fun) :-
    atom(Fun), !,
    retractall(he_compiled_goal_resolution(Fun, _, _)),
    retractall(he_compiled_goal_no_resolution(Fun, _)).
he_invalidate_compiled_goal_resolution(_).

he_invalidate_runtime_callable_head_cache(Fun) :-
    atom(Fun), !,
    retractall(he_runtime_callable_head_cache(Fun)).
he_invalidate_runtime_callable_head_cache(_).

he_invalidate_call_partial_arity_cache(Fun) :-
    atom(Fun), !,
    retractall(he_call_partial_arity_cache(Fun, _, _)).
he_invalidate_call_partial_arity_cache(_).

he_space_fact_added_hook('&self', [=, [Fun|_], _]) :-
    atom(Fun), !,
    he_invalidate_compiled_goal_resolution(Fun),
    he_invalidate_runtime_callable_head_cache(Fun),
    he_invalidate_call_partial_arity_cache(Fun).
he_space_fact_removed_hook('&self', [=, [Fun|_], _]) :-
    atom(Fun), !,
    he_invalidate_compiled_goal_resolution(Fun),
    he_invalidate_runtime_callable_head_cache(Fun),
    he_invalidate_call_partial_arity_cache(Fun).
he_fun_registered_hook(Fun) :-
    atom(Fun), !,
    he_invalidate_runtime_callable_head_cache(Fun),
    he_invalidate_call_partial_arity_cache(Fun).
he_fun_removed_hook(Fun) :-
    atom(Fun), !,
    he_invalidate_runtime_callable_head_cache(Fun),
    he_invalidate_compiled_goal_resolution(Fun),
    he_invalidate_call_partial_arity_cache(Fun).

he_compiled_goal_user_functor(Fun, Arity, UserFun) :-
    he_compiled_goal_resolution(Fun, Arity, UserFun), !.
he_compiled_goal_user_functor(Fun, Arity, _) :-
    he_compiled_goal_no_resolution(Fun, Arity), !,
    fail.
he_compiled_goal_user_functor(Fun, Arity, UserFun) :-
    metta_user_functor(Fun, UserFun),
    current_predicate(UserFun/Arity), !,
    assertz(he_compiled_goal_resolution(Fun, Arity, UserFun)).
he_compiled_goal_user_functor(Fun, Arity, _) :-
    assertz(he_compiled_goal_no_resolution(Fun, Arity)),
    fail.

he_compiled_equation_goal([Fun|Args], Out, Goal) :-
    he_profile_enabled,
    atom(Fun),
    length(Args, Arity),
    he_eq_fact(Fun, Arity, _, _),
    metta_user_functor(Fun, UserFun),
    append(Args, [Out], CallArgs),
    Goal =.. [UserFun|CallArgs].
he_compiled_user_goal(Call, Out, Goal) :-
    he_compiled_equation_goal(Call, Out, Goal).
he_compiled_user_goal([Fun|Args], Out, Goal) :-
    he_profile_enabled,
    atom(Fun),
    fun(Fun),
    append(Args, [Out], CallArgs),
    length(CallArgs, Arity),
    he_compiled_goal_user_functor(Fun, Arity, UserFun),
    Goal =.. [UserFun|CallArgs].

he_build_user_call_or_eval(Call, Out, Goal) :-
    he_profile_enabled,
    he_call_has_fun_meta(Call),
    Call = [Fun|Args],
    atom(Fun),
    metta_user_functor(Fun, UserFun),
    append(Args, [Out], CallArgs),
    Goal =.. [UserFun|CallArgs], !.
he_build_user_call_or_eval(Call, Out, he_eval_or_reduce(Call, Out)).

he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    var(Fun), !,
    Out = [Fun|Args].
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    nonvar(Fun),
    \+ he_runtime_callable_head(Fun), !,
    Out = [Fun|Args].
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    py_call_callable(Fun, Args, Out), !.
he_eval_or_reduce([foldl, Func, List, Init], Out) :-
    he_profile_enabled,
    is_list(List), !,
    he_foldl_reduce(List, Func, Init, Out).
he_eval_or_reduce([maplist, Func, List], Out) :-
    he_profile_enabled,
    is_list(List), !,
    he_maplist_reduce(List, Func, Out).
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    he_compiled_equation_goal(Call, Out, Goal), !,
    catch(call(Goal), _, fail).
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    he_compiled_user_goal(Call, Out, Goal), !,
    he_call_compiled_or_self(Call, Goal, Out).
he_eval_or_reduce(Call, Out) :-
    he_call_has_equation(Call), !,
    catch(match('&self', [=, Call, Body], Body, _), _, fail),
    eval(Body, Out).
he_eval_or_reduce(Call, Out) :-
    reduce(Call, Reduced),
    ( he_profile_enabled,
      Reduced =@= Call,
      he_apply_zero_arg_callable(Call, Out)
    -> true
    ;  Out = Reduced
    ).

he_apply_zero_arg_callable([Fun|Args], Out) :-
    atom(Fun),
    Args \= [],
    he_eval_or_reduce([Fun], Callable),
    he_apply_callable_result(Callable, Args, Out).

he_apply_callable_result(partial(Fun, Bound), Args, Out) :-
    append(Bound, Args, AllArgs),
    he_eval_or_reduce([Fun|AllArgs], Out).
he_apply_callable_result(Fun, Args, Out) :-
    atom(Fun),
    fun(Fun),
    he_eval_or_reduce([Fun|Args], Out).
he_apply_callable_result(Expr, Args, Out) :-
    is_list(Expr),
    Expr \= [],
    he_eval_or_reduce(Expr, Callable),
    Callable \=@= Expr,
    he_apply_callable_result(Callable, Args, Out).

he_runtime_callable_head(Fun) :-
    atom(Fun),
    he_runtime_callable_head_cache(Fun), !.
he_runtime_callable_head(Fun) :-
    atom(Fun),
    fun(Fun), !,
    assertz(he_runtime_callable_head_cache(Fun)).
he_runtime_callable_head(Fun) :-
    atom(Fun),
    he_constructor_symbol(Fun), !,
    assertz(he_runtime_callable_head_cache(Fun)).
he_runtime_callable_head(Fun) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    is_list(Metas), Metas \= [], !,
    assertz(he_runtime_callable_head_cache(Fun)).
he_runtime_callable_head(Fun) :-
    py_resolve_value(Fun, Callable),
    py_callable(Callable), !.
he_runtime_callable_head(Fun) :-
    compound(Fun),
    Fun = partial(_, _), !.

he_call_or_self(Fun, Args, Out) :-
    \+ he_call_is_partial_arity(Fun, Args),
    append(Args, [Out], CallArgs),
    Goal =.. [Fun|CallArgs],
    length(CallArgs, Arity),
    \+ (current_op(_, _, Fun), Arity =< 2),
    catch(call(Goal), _, fail).
he_call_or_self(Fun, Args, Out) :-
    he_profile_enabled,
    he_call_is_partial_arity(Fun, Args), !,
    Out = partial(Fun, Args).
he_call_or_self(Fun, Args, Out) :-
    append(Args, [_], CallArgs),
    Goal =.. [Fun|CallArgs],
    \+ catch(once(call(Goal)), _, fail),
    he_profile_enabled,
    he_returns_self_on_failure(Fun),
    Out = [Fun|Args].

he_call_is_partial_arity(Fun, Args) :-
    atom(Fun),
    length(Args, Supplied),
    he_call_partial_arity_decision(Fun, Supplied, Decision),
    Decision == partial.

he_call_partial_arity_decision(Fun, Supplied, Decision) :-
    he_call_partial_arity_cache(Fun, Supplied, Decision), !.
he_call_partial_arity_decision(Fun, Supplied, Decision) :-
    SuppliedOutArity is Supplied + 1,
    ( he_call_known_full_out_arity(Fun, SuppliedOutArity, FullOutArity),
      FullOutArity > SuppliedOutArity
    -> Decision = partial
    ;  Decision = none
    ),
    assertz(he_call_partial_arity_cache(Fun, Supplied, Decision)).

he_call_known_full_out_arity(Fun, _, FullOutArity) :-
    he_builtin_type(Fun, TypeChain),
    TypeChain = [->|TypeItems],
    length(TypeItems, FullOutArity).
he_call_known_full_out_arity(Fun, _, FullOutArity) :-
    catch(arity(Fun, FullOutArity), _, fail).
he_call_known_full_out_arity(Fun, SuppliedOutArity, FullOutArity) :-
    he_profile_enabled,
    he_eq_fact(Fun, HeadArity, _, _),
    FullOutArity is HeadArity + 1,
    FullOutArity > SuppliedOutArity.
he_call_known_full_out_arity(Fun, SuppliedOutArity, FullOutArity) :-
    MinArity is SuppliedOutArity + 1,
    he_partial_arity_probe_limit(MaxArity),
    between(MinArity, MaxArity, FullOutArity),
    current_predicate(Fun/FullOutArity).

he_partial_arity_probe_limit(32).

he_call_compiled_or_self(Call, Goal, _) :-
    he_call_has_equation(Call), !,
    catch(call(Goal), _, fail).
he_call_compiled_or_self(Call, Goal, Out) :-
    ( catch(call(Goal), _, fail)
    ; Out = Call ).

he_maybe_register_specialization_types(Fun, Args, TypeChains) :-
    he_profile_enabled,
    atom(Fun),
    findall(Arg, (member(Arg, Args), atom(Arg), fun(Arg)), BindSet),
    BindSet \= [], !,
    format(atom(SpecName), "~w_Spec_~w", [Fun, BindSet]),
    register_fun(SpecName),
    length(Args, N),
    Arity is N + 1,
    ( arity(SpecName, Arity) -> true ; assertz(arity(SpecName, Arity)) ),
    forall(member(TypeChain, TypeChains),
           he_add_space_fact_if_absent([':', SpecName, TypeChain])).
he_maybe_register_specialization_types(_, _, _).

he_add_space_fact_if_absent(Fact) :-
    once(match('&self', Fact, Fact, _)), !.
he_add_space_fact_if_absent(Fact) :-
    add_sexp('&self', Fact),
    he_note_space_fact_added('&self', Fact).

he_maplist_reduce([], _Func, []).
he_maplist_reduce([X|Xs], Func, [Y|Ys]) :-
    reduce([Func, X], Y),
    he_maplist_reduce(Xs, Func, Ys).

he_foldl_reduce([], _Func, Acc, Acc).
he_foldl_reduce([X|Xs], Func, Acc0, Out) :-
    he_eval_or_reduce([Func, X, Acc0], Acc1),
    he_foldl_reduce(Xs, Func, Acc1, Out).
