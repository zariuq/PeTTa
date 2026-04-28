:- discontiguous he_translate_special/5.

he_clause_constrains_args(ConstrainArgs) :-
    ConstrainArgs.

he_lower_clause_body(Expr, Goals, Out) :-
    he_clause_data_skeleton(Expr, Out, Goals), !.

he_clause_data_skeleton(X, X, []) :-
    (var(X); atomic(X)), !.
he_clause_data_skeleton([Head|Args], [Head|OutArgs], Goals) :-
    atom(Head),
    he_clause_noncallable_head(Head), !,
    he_clause_data_args(Args, OutArgs, Goals).

he_clause_data_args([], [], []).
he_clause_data_args([Arg|Args], [OutArg|OutArgs], Goals) :-
    he_clause_data_arg(Arg, OutArg, G1),
    he_clause_data_args(Args, OutArgs, G2),
    append(G1, G2, Goals).

he_clause_data_arg(Expr, Out, Goals) :-
    he_clause_data_skeleton(Expr, Out, Goals), !.
he_clause_data_arg(Expr, Out, Goals) :-
    translate_expr(Expr, Goals, Out).

he_clause_noncallable_head(Head) :-
    atom(Head),
    \+ he_clause_callable_head(Head).

he_clause_callable_head(Head) :-
    fun(Head), !.
he_clause_callable_head(Head) :-
    translator_rule(Head), !.
he_clause_callable_head(Head) :-
    memberchk(Head,
              [cut, superpose, collapse, test, once, hyperpose, with_mutex,
               transaction, progn, prog1, if, case, let, chain, 'let*',
               sealed, 'forall', 'foldall', 'foldl-atom', 'map-atom',
               'filter-atom', '|->', match, translatePredicate, call,
               reduce, eval, quote, 'catch', function, return, lambda,
               switch, metta, select, 'context-space', 'search-policy',
               'Error', assertEqualToResult, assertAlphaEqualToResult,
               assertPeTTaTest, unify, 'add-reduct', evalc, unquote,
               'noreduce-eq']).

he_reduce_known_fun(F, Args, Out) :-
    he_profile_enabled,
    he_compiled_user_goal([F|Args], Out, Goal), !,
    he_call_compiled_or_self([F|Args], Goal, Out).
he_reduce_known_fun(F, Args, Out) :-
    he_profile_enabled, !,
    he_call_or_self(F, Args, Out).
he_reduce_known_fun(F, Args, Out) :-
    append(Args,[Out],CallArgs),
    Goal =.. [F|CallArgs],
    catch(call(Goal),_,fail).

he_reduce_missing_fun(F, Args, Out) :-
    he_profile_enabled,
    he_compiled_user_goal([F|Args], Out, Goal), !,
    he_call_compiled_or_self([F|Args], Goal, Out).
he_reduce_missing_fun(F, Args, Out) :-
    he_profile_enabled,
    he_call_has_equation([F|Args]), !,
    he_eval_or_reduce([F|Args], Out).
he_reduce_missing_fun(F, Args, Out) :-
    he_profile_enabled, !,
    Out = [F|Args].
he_reduce_missing_fun(F, Args, partial(F, Args)).

he_eval_goal(Arg, Out, he_eval_special(Arg, Out)) :-
    he_profile_enabled, !.
he_eval_goal(Arg, Out, eval(Arg, Out)).

he_smart_known_fun(Fun, AllAVs, Out, Inner, T, GsH, IsPartial, Bound, Goals) :-
    he_profile_enabled,
    findall(TypeChain,
            catch(match('&self', [':', Fun, TypeChain], TypeChain, TypeChain), _, fail),
            TypeChains0),
    alpha_list_to_set(TypeChains0, TypeChains),
    include(he_arrow_typechain, TypeChains, ArrowTypeChains),
    ArrowTypeChains \= [],
    !,
    ( IsPartial -> append(Bound, T, AllRawArgs) ; AllRawArgs = T ),
    include(he_typechain_arity_matches(AllRawArgs), ArrowTypeChains, MatchingArity),
    ( MatchingArity == []
    -> append(Inner, [he_call_typed(Fun, AllAVs, ArrowTypeChains, Out)], Goals)
    ; maplist({Fun,AllRawArgs,GsH,Out}/[TypeChain,BranchGoal]>>(
          he_typed_functioncall_branch(Fun, AllRawArgs, GsH, TypeChain, Out, BranchGoal)),
          MatchingArity,
          Branches),
      disj_list(Branches, Disj),
      Goals = [Disj]
    ).
he_smart_known_fun(Fun, AllAVs, Out, Inner, _T, _GsH, _IsPartial, _Bound, Goals) :-
    he_profile_enabled, !,
    he_build_user_call_or_eval([Fun|AllAVs], Out, HeGoal),
    append(Inner, [HeGoal], Goals).
he_smart_known_fun(Fun, AllAVs, Out, Inner, T, GsH, IsPartial, Bound, Goals) :-
    findall(TypeChain, catch(match('&self', [':', Fun, TypeChain], TypeChain, TypeChain), _, fail), TypeChains),
    ( TypeChains \= []
    -> maplist({Fun,T,GsH,IsPartial,Bound,Out}/[TypeChain,BranchGoal]>>(
           typed_functioncall_branch(Fun, TypeChain, T, GsH, IsPartial, Bound, Out, BranchGoal)), TypeChains, Branches),
       disj_list(Branches, Disj),
       Goals = [Disj]
    ; build_call_or_partial(Fun, AllAVs, Out, Inner, [], Goals)
    ).

he_unknown_head_dispatch(HV, AVs, Out, Inner, Goals) :-
    he_profile_enabled,
    \+ ( atomic(HV), \+ atom(HV) ), !,
    append(Inner, [he_eval_or_reduce([HV|AVs], Out)], Goals).

he_callable_head_dispatch(HV, AVs, Out, Inner, Goals) :-
    he_profile_enabled,
    \+ ( atomic(HV), \+ atom(HV) ),
    append(Inner, [py_call_callable(HV, AVs, Out)], Goals).

he_partial_or_data(Fun, AVs, Out) :-
    he_profile_enabled,
    fun(Fun), !,
    Out = partial(Fun, AVs).
he_partial_or_data(Fun, AVs, Out) :-
    he_profile_enabled, !,
    Out = [Fun|AVs].
he_partial_or_data(Fun, AVs, partial(Fun, AVs)).

he_eval_data_term([F|As], Goals, Val) :-
    he_profile_enabled,
    \+ atom(F),
    he_callable_data_head(F), !,
    translate_expr([F|As], Goals, Val).

he_callable_data_head(F) :-
    var(F), !.
he_callable_data_head(F) :-
    compound(F),
    \+ is_list(F), !.
he_callable_data_head(F) :-
    is_list(F),
    F = [Head|_],
    he_callable_data_head_functor(Head).

he_callable_data_head_functor(Head) :-
    var(Head), !.
he_callable_data_head_functor(Head) :-
    is_list(Head),
    he_callable_data_head(Head), !.
he_callable_data_head_functor(Head) :-
    atom(Head),
    ( fun(Head)
    ; Head == '|->'
    ; Head == lambda
    ; memberchk(Head, [if, let, chain, 'let*', eval, collapse])
    ).

he_constrain_args(X, X, []) :-
    (var(X); atomic(X)), !.
he_constrain_args([F, A, B], Out, Goals) :-
    nonvar(F),
    F == cons,
    he_constrain_args(A, A1, G1),
    he_constrain_args(B, B1, G2),
    Out = [A1|B1],
    append(G1, G2, Goals), !.
he_constrain_args([F|Args], Var, Goals) :-
    atom(F),
    ( fun(F)
    ; memberchk(F, [if, let, chain, 'let*', eval, collapse])
    ), !,
    translate_expr([F|Args], GoalsExpr, Var),
    flatten(GoalsExpr, Goals).
he_constrain_args(In, Out, Goals) :-
    maplist(he_constrain_args, In, Out, NestedGoalsList),
    flatten(NestedGoalsList, Goals), !.

he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'collapse-bind',
    T = [E], !,
    translate_expr_to_conj(E, Conj, EV),
    append(GsH, [findall(EV, Conj, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'superpose-bind',
    T = [E], !,
    translate_expr(E, GsE, EV),
    append([GsH, GsE, [member(Out, EV)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == '==',
    T = [[], [collapse, [once, [match, SpaceExpr, Pattern, Body]]]], !,
    he_translate_match_once_truth_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == '==',
    T = [[collapse, [once, [match, SpaceExpr, Pattern, Body]]], []], !,
    he_translate_match_once_truth_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == unify,
    T = [A, B, Then, Else], !,
    translate_expr(A, Ga, Av),
    translate_expr(B, Gb, Bv),
    translate_expr_to_conj(Then, ConT, Tv),
    translate_expr_to_conj(Else, ConE, Ev),
    build_branch(ConT, Tv, Out, BT),
    build_branch(ConE, Ev, Out, BE),
    append([GsH, Ga, Gb, [(he_unify_success(Av, Bv) -> BT ; BE)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'add-reduct',
    T = [Space, Form], !,
    translate_expr(Space, GsS, S),
    append([GsH, GsS, [he_native_add_reduct(S, Form, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == unquote,
    T = [[quote, Expr]], !,
    translate_expr(Expr, GsExpr, Out),
    append(GsH, GsExpr, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == unquote,
    T = [Expr], !,
    Out = [unquote, Expr],
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'noreduce-eq',
    T = [A, B], !,
    ( A == B -> Out = true ; Out = false ),
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == let,
    T = [Pat, Val, In], !,
    he_constrain_args(Pat, Pv, Gp),
    translate_expr(Val, Gv, V),
    translate_expr(In, Gi, Out),
    append([GsH, Gv, [(Pv = V)], Gp, Gi], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == chain,
    T = [Val, Pat, In], !,
    he_constrain_args(Pat, Pv, Gp),
    translate_expr(Val, Gv, V),
    translate_expr(In, Gi, Out),
    append([GsH, Gv, [(Pv = V)], Gp, Gi], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertEqual,
    T = [Expr, Expected], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(Expected, ExpConj, ExpVal),
    Goal = ( findall(ExprVal, ExprConj, Actuals),
             findall(ExpVal, ExpConj, Expecteds),
             he_assert_set_results([assertEqual, Expr, Expected], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertEqualToResult,
    T = [Expr, ExpectedTuple], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( findall(ExprVal, ExprConj, Actuals),
             he_expected_tuple_results(ExpectedTuple, Expecteds),
             he_assert_same_results([assertEqualToResult, Expr, ExpectedTuple], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertAlphaEqualToResult,
    T = [Expr, ExpectedTuple], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( findall(ExprVal, ExprConj, Actuals),
             he_expected_tuple_results(ExpectedTuple, Expecteds),
             he_assert_same_results([assertAlphaEqualToResult, Expr, ExpectedTuple], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertPeTTaTest,
    T = [Expr, Expected], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr(Expected, ExpGoals, ExpVal),
    ActualGoal = ( ( once((ExprConj, FirstActual = ExprVal)),
                     he_petta_test_matches(FirstActual, ExpVal) )
                   -> Actual = FirstActual
                   ;  findall(ExprVal, ExprConj, Results),
                      ( Results = [Actual] -> true ; Actual = Results ) ),
    AssertGoal = he_assert_petta_test([assertPeTTaTest, Expr, Expected],
                                      Actual, ExpVal, Out),
    append([GsH, ExpGoals, [ActualGoal, AssertGoal]], Goals).

he_translate_match_once_truth_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals) :-
    ( Body == true ; Body == 'True' ),
    translate_expr(SpaceExpr, GsS, S),
    append([GsH, GsS, [he_match_once_truth_empty(S, Pattern, Out)]], Goals).

he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'Error', !,
    Out = ['Error'|T],
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'search-policy',
    T = [Policy], !,
    Goals = GsH,
    Out = ['search-policy', Policy].
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == select,
    T = [X], !,
    translate_expr_to_conj(X, Conj, Val),
    append(GsH, [once((Conj, Out = Val))], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == select,
    T = [_Policy, X], !,
    translate_expr_to_conj(X, Conj, Val),
    append(GsH, [once((Conj, Out = Val))], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == function,
    T = [Body], !,
    translate_expr_to_conj(Body, BodyConj, BodyOut),
    Goal = catch((BodyConj, Out = BodyOut),
                 he_return(Returned),
                 Out = Returned),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == return,
    T = [Expr], !,
    append(GsH, [throw(he_return(Expr))], Goals),
    Out = Expr.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'context-space',
    T = [], !,
    Goals = GsH,
    Out = '&self'.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == metta,
    T = [Atom, Type, Space], !,
    translate_expr(Space, GsS, SpaceV),
    translate_expr(Type, GsT, TypeV),
    append([GsH, GsS, GsT, [he_metta_one(Atom, TypeV, SpaceV, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == switch,
    T = [KeyExpr, PairsExpr], !,
    translate_expr(KeyExpr, Gk, Kv),
    translate_case(PairsExpr, Kv, Out, IfGoal, KeyGoal),
    append([GsH, Gk, KeyGoal, [IfGoal]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == lambda,
    T = [Var, Body], !,
    Out = [lambda, Var, Body],
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'with-space-snapshot',
    T = [Snapshot, SpaceExpr, Body], !,
    translate_expr(SpaceExpr, GsS, Space),
    translate_expr_to_conj(Body, BodyConj, BodyOut),
    append([GsH, GsS, [he_with_space_snapshot(Snapshot, Space, BodyConj, BodyOut, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'import!',
    T = [Space, File], !,
    translate_expr(Space, GsS, S),
    append([GsH, GsS, ['import!'(S, File, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == evalc,
    T = [Arg, Space], !,
    translate_expr(Space, GsS, SpaceV),
    append([GsH, GsS, [he_metta_one(Arg, '%Undefined%', SpaceV, Out)]], Goals).

he_native_helper_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    atom(HV),
    he_native_helper(HV, Native),
    translate_args(RawArgs, GsArgs, AVs),
    append(AVs, [Out], CallArgs),
    Goal =.. [Native|CallArgs],
    append([GsH, GsArgs, [Goal]], Goals).

he_typed_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    ( atom(HV), Fun = HV, AllRawArgs = RawArgs
    ; compound(HV), HV = partial(Fun, Bound), append(Bound, RawArgs, AllRawArgs)
    ),
    he_function_typechains(Fun, TypeChains),
    include(he_arrow_typechain, TypeChains, ArrowTypeChains),
    ArrowTypeChains \= [],
    include(he_typechain_arity_matches(AllRawArgs), ArrowTypeChains, MatchingArity),
    ( MatchingArity == []
    -> ( he_typed_partial_candidate(AllRawArgs, ArrowTypeChains)
       -> translate_args(AllRawArgs, GsArgs, AVs),
          append([GsH, GsArgs, [he_partial_or_data(Fun, AVs, Out)]], Goals)
       ;  append(GsH, [he_call_typed(Fun, AllRawArgs, ArrowTypeChains, Out)], Goals)
       )
    ; maplist({Fun,AllRawArgs,GsH,Out}/[TypeChain,BranchGoal]>>(
          he_typed_functioncall_branch(Fun, AllRawArgs, GsH, TypeChain, Out, BranchGoal)),
          MatchingArity,
          Branches),
      disj_list(Branches, Disj),
      Goals = [Disj]
    ).

he_typed_partial_candidate(Args, TypeChains) :-
    length(Args, Supplied),
    member(TypeChain, TypeChains),
    TypeChain = [->|TypeItems],
    length(TypeItems, ItemCount),
    ArgCount is ItemCount - 1,
    Supplied < ArgCount, !.

he_typed_functioncall_branch(Fun, RawArgs, GsH, TypeChain, Out, BranchGoal) :-
    TypeChain = [->|TypeItems],
    append(ArgTypes, [_], TypeItems),
    translate_he_args_by_type(RawArgs, ArgTypes, GsArgs, AVs),
    append(GsH, GsArgs, Inner),
    append(Inner, [he_call_typed(Fun, AVs, [TypeChain], Out)], Goals),
    goals_list_to_conj(Goals, BranchGoal).

translate_he_args_by_type([], [], [], []) :- !.
translate_he_args_by_type([A|As], [T|Ts], GsOut, [AV|AVs]) :-
    translate_he_arg_by_type(A, T, GsA, AV),
    translate_he_args_by_type(As, Ts, GsRest, AVs),
    append(GsA, GsRest, GsOut).

translate_he_arg_by_type(A, Type, [], A) :-
    ( nonvar(Type),
      he_arg_stays_data(A, Type)
    ; var(Type),
      ( var(A)
      ; is_list(A),
        A = [Head|_],
        ( var(Head)
        ; atom(Head),
          \+ fun(Head)
        )
      )
    ), !.
translate_he_arg_by_type(A, _, Goals, AV) :-
    translate_expr(A, Goals, AV).

he_arg_stays_data(_, 'Atom') :- !.
he_arg_stays_data(A, _) :-
    var(A), !.
he_arg_stays_data(A, Type) :-
    he_literal_metatype(A, Type).

he_literal_metatype(A, 'Variable') :-
    var(A), !.
he_literal_metatype(A, 'Grounded') :-
    ( number(A) ; string(A) ; A == true ; A == false ), !.
he_literal_metatype(A, 'Grounded') :-
    atom(A),
    fun(A), !.
he_literal_metatype(A, 'Expression') :-
    is_list(A), !.
he_literal_metatype(A, 'Symbol') :-
    atom(A), !.
