% HE-profile overrides for PeTTa's internal MeTTa -> Prolog runtime compiler.
% This is not the canonical file-to-file PeTTa <-> HE translator; that lives
% in /home/zar/claude/hyperon/translators/.

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
    is_list(HV),
    \+ he_callable_data_head(HV), !,
    Out = [HV|AVs],
    Goals = Inner.

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
    atom(F),
    he_symbolic_data_functor(F), !,
    eval_data_list([F|As], Goals, Val).
he_eval_data_term([F|As], Goals, Val) :-
    he_profile_enabled,
    nonvar(F),
    \+ atom(F),
    he_callable_data_head(F), !,
    translate_expr([F|As], Goals, Val).

he_superpose_effect_branches([], []).
he_superpose_effect_branches([Expr|Exprs], [branch(Conj, Val)|Branches]) :-
    translate_expr_to_conj(Expr, Conj, Val),
    he_superpose_effect_branches(Exprs, Branches).

he_run_superpose_branches(Branches, Out) :-
    findall(Result,
            ( member(branch(Conj, Val), Branches),
              call(Conj),
              he_visible_result(Val),
              Result = Val
            ),
            Results),
    member(Out, Results).

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
    ( he_head_may_denote_callable(Head)
    ; Head == '|->'
    ; Head == lambda
    ; memberchk(Head, [if, let, chain, 'let*', eval, collapse])
    ).

he_nonself_get_atoms_collapse_goal(he_collect_visible_results('get-atoms'(Space, Atom), Atom, Value),
                                   Space,
                                   Value) :-
    nonvar(Space),
    Space \== '&self'.

he_bound_import_typed_heads(Atoms, TypedHeads) :-
    findall(Fun,
            ( member([':', Fun, _], Atoms),
              atom(Fun)
            ),
            TypedHeads0),
    sort(TypedHeads0, TypedHeads).

he_bound_import_head_var(HeadVars, Var) :-
    var(Var),
    member(Candidate, HeadVars),
    Candidate == Var.

he_bound_import_ground_literal(Term) :-
    nonvar(Term),
    atomic(Term).

he_bound_import_eq_guard(L, R, _HeadVars, true) :-
    L =@= R, !.
he_bound_import_eq_guard(L, R, HeadVars, false) :-
    he_bound_import_head_var(HeadVars, L),
    he_bound_import_ground_literal(R), !.
he_bound_import_eq_guard(L, R, HeadVars, false) :-
    he_bound_import_head_var(HeadVars, R),
    he_bound_import_ground_literal(L), !.
he_bound_import_eq_guard(L, R, _HeadVars, false) :-
    he_bound_import_ground_literal(L),
    he_bound_import_ground_literal(R),
    L \=@= R, !.

he_bound_import_visible_body(Term, HeadVars, Norm) :-
    nonvar(Term),
    is_list(Term),
    Term = [if, ['==', L, R], Then, Else],
    he_bound_import_eq_guard(L, R, HeadVars, Decision), !,
    ( Decision == true -> Target = Then ; Target = Else ),
    he_bound_import_visible_body(Target, HeadVars, Norm).
he_bound_import_visible_body(Term, _HeadVars, Term) :-
    var(Term), !.
he_bound_import_visible_body(Term, HeadVars, [Head|NormArgs]) :-
    nonvar(Term),
    is_list(Term),
    Term = [Head|Args],
    !,
    maplist({HeadVars}/[Arg,NormArg]>>he_bound_import_visible_body(Arg, HeadVars, NormArg),
            Args,
            NormArgs).
he_bound_import_visible_body(Term, _HeadVars, Term).

he_bound_import_visible_atom(TypedHeads, Atom, [=, Head, NormBody]) :-
    nonvar(Atom),
    is_list(Atom),
    Atom = [=, Head, Body],
    is_list(Head),
    Head = [Fun|HeadVars],
    atom(Fun),
    \+ memberchk(Fun, TypedHeads),
    he_bound_import_visible_body(Body, HeadVars, NormBody), !.
he_bound_import_visible_atom(_TypedHeads, Atom, Atom).

he_normalize_nonself_get_atoms_bound_value(Value, Normalized) :-
    is_list(Value), !,
    he_bound_import_typed_heads(Value, TypedHeads),
    maplist(he_bound_import_visible_atom(TypedHeads), Value, Normalized).
he_normalize_nonself_get_atoms_bound_value(Value, Value).

he_nonself_equation_body_match_goal((A, _)) :-
    he_nonself_equation_body_match_goal(A), !.
he_nonself_equation_body_match_goal((_, B)) :-
    he_nonself_equation_body_match_goal(B), !.
he_nonself_equation_body_match_goal(match(Space, Pattern, _Body, _)) :-
    nonvar(Space),
    Space \== '&self',
    nonvar(Pattern),
    is_list(Pattern),
    Pattern = [=|_].

he_block_nonself_equation_body_binding(ValConj, Value) :-
    he_nonself_equation_body_match_goal(ValConj),
    is_list(Value),
    Value = [Head|_],
    atom(Head),
    \+ memberchk(Head, [=, ':', ',', 'Error']).

he_bind_visible_results(he_eval_special(Arg, Value), Value, Pattern, PatConj, InConj, InValue, Out) :-
    he_eval_likely_singleton(Arg), !,
    once((
        he_eval_special(Arg, Value),
        \+ he_error_atom(Value),
        Pattern = Value,
        call(PatConj),
        call(InConj),
        Out = InValue
    )).
he_bind_visible_results(ValConj, Value, Pattern, PatConj, InConj, InValue, Out) :-
    he_nonself_get_atoms_collapse_goal(ValConj, _Space, Value),
    !,
    State = state(no_success),
    ( call(ValConj),
      \+ he_error_atom(Value),
      he_normalize_nonself_get_atoms_bound_value(Value, BoundValue),
      nb_setarg(1, State, success),
      Pattern = BoundValue,
      call(PatConj),
      call(InConj),
      Out = InValue
    ; arg(1, State, no_success),
      call(ValConj),
      he_error_atom(Value),
      Out = Value
    ).
he_bind_visible_results(ValConj, Value, Pattern, PatConj, InConj, InValue, Out) :-
    State = state(no_success),
    ( call(ValConj),
      \+ he_error_atom(Value),
      \+ he_block_nonself_equation_body_binding(ValConj, Value),
      nb_setarg(1, State, success),
      Pattern = Value,
      call(PatConj),
      call(InConj),
      Out = InValue
    ; arg(1, State, no_success),
      call(ValConj),
      he_error_atom(Value),
      Out = Value
    ).

he_eval_likely_singleton(Arg) :-
    ground(Arg),
    \+ he_expr_may_be_nondet(Arg).

% Keep the HE-spec-shaped NoReturn boundary explicit at the function surface.
% The strict harness classifies the upstream variable-leak witness as an
% accepted oracle quirk rather than changing this runtime contract.
he_function_no_return_result(SubjectBody, ['Error', [function, SubjectBody], 'NoReturn']).

he_function_body_or_no_return(BodyConj, SubjectBody, BodyOut, Out) :-
    ( BodyConj
    -> he_function_no_return_result(SubjectBody, Out)
    ;  he_function_no_return_result(SubjectBody, Out)
    ),
    ignore(BodyOut == BodyOut).

he_expr_may_be_nondet(Expr) :-
    var(Expr), !.
he_expr_may_be_nondet(Expr) :-
    atomic(Expr), !,
    fail.
he_expr_may_be_nondet([Head|_Args]) :-
    var(Head), !.
he_expr_may_be_nondet([Head|_Args]) :-
    atom(Head),
    memberchk(Head,
              [superpose, hyperpose, collapse, once, match, select,
               'collapse-bind', 'superpose-bind', metta, evalc]),
    !.
he_expr_may_be_nondet([Head|_Args]) :-
    atom(Head),
    catch(nb_getval(Head, Metas), _, fail),
    is_list(Metas),
    Metas \= [],
    \+ he_fun_head_likely_singleton(Head), !.
he_expr_may_be_nondet([_Head|Args]) :-
    member(Arg, Args),
    he_expr_may_be_nondet(Arg), !.

he_fun_head_likely_singleton(Head) :-
    catch(nb_getval(Head, Metas), _, fail),
    include(he_fun_meta_entry, Metas, FunMetas),
    FunMetas = [fun_meta(_PatternArgs, BodyExpr)],
    \+ he_expr_contains_nondet_surface(BodyExpr).

he_fun_meta_entry(fun_meta(_, _)).

he_expr_contains_nondet_surface(Expr) :-
    var(Expr), !,
    fail.
he_expr_contains_nondet_surface(Expr) :-
    atomic(Expr), !,
    fail.
he_expr_contains_nondet_surface([Head|_Args]) :-
    atom(Head),
    memberchk(Head,
              [superpose, hyperpose, collapse, once, match, select,
               'collapse-bind', 'superpose-bind', metta, evalc]),
    !.
he_expr_contains_nondet_surface([_Head|Args]) :-
    member(Arg, Args),
    he_expr_contains_nondet_surface(Arg), !.

he_bind_visible_or_cut_goals(GsH, !, V, Pattern, PatConj, InConj, InValue, Out, Goals) :-
    !,
    append([GsH, [!, Pattern = V, PatConj, InConj, Out = InValue]], Goals).
he_bind_visible_or_cut_goals(GsH, ValConj, V, Pattern, PatConj, InConj, InValue, Out, Goals) :-
    append([GsH, [he_bind_visible_results(ValConj, V, Pattern, PatConj, InConj, InValue, Out)]], Goals).

he_strict_special_surface_arity(eval, 1).
he_strict_special_surface_arity('import!', 2).
he_strict_special_surface_arity(evalc, 2).
he_strict_special_surface_arity(sealed, 2).
he_strict_special_surface_arity('collapse-bind', 1).
he_strict_special_surface_arity('superpose-bind', 1).
he_strict_special_surface_arity(quote, 1).

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
    he_profile_enabled,
    atom(HV),
    he_strict_special_surface_arity(HV, ExpectedArity),
    length(T, ActualArity),
    ActualArity =\= ExpectedArity,
    !,
    Out = ['Error', [HV|T], 'IncorrectNumberOfArguments'],
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'collapse-bind',
    T = [E],
    term_variables(E, Vars), !,
    translate_expr_to_conj(E, Conj, EV),
    append(GsH, [he_collect_bind_packets(Conj, EV, Vars, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'superpose-bind',
    T = [E], !,
    translate_expr(E, GsE, EV),
    append([GsH, GsE, [he_superpose_bind_member(EV, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == '==',
    T = [[], [collapse, [once, [match, SpaceExpr, Pattern, Body]]]], !,
    he_translate_match_once_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == '==',
    T = [[collapse, [once, [match, SpaceExpr, Pattern, Body]]], []], !,
    he_translate_match_once_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == unify,
    T = [A, B, Then, Else], !,
    eval_data_term(A, Ga, Av),
    eval_data_term(B, Gb, Bv),
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
    HV == quote,
    T = [Expr], !,
    Out = [quote, Expr],
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'noreduce-eq',
    T = [A, B], !,
    ( A == B -> Out = true ; Out = false ),
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == let,
    T = [Pat, CollapseExpr, SizeExpr],
    var(Pat),
    nonvar(CollapseExpr),
    CollapseExpr = [collapse, Expr],
    nonvar(SizeExpr),
    SizeExpr = ['size-atom', SizeArg],
    SizeArg == Pat, !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    append(GsH, [he_count_visible_results(ExprConj, ExprVal, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == let,
    T = [Pat, CollapseExpr, FoldExpr],
    var(Pat),
    nonvar(CollapseExpr),
    CollapseExpr = [collapse, Expr],
    nonvar(FoldExpr),
    FoldExpr = [foldl, Func, FoldArg, InitExpr],
    FoldArg == Pat, !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(InitExpr, InitConj, InitValue),
    exclude(==(true), [InitConj], VisibleConjs),
    append(GsH, VisibleConjs, MidGoals),
    append(MidGoals, [he_fold_visible_results(ExprConj, ExprVal, Func, InitValue, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == let,
    T = [Pat, CollapseExpr, In],
    var(Pat),
    nonvar(CollapseExpr),
    CollapseExpr = [collapse, Expr],
    nonvar(In),
    In = [let, FoldPat, FoldExpr, Rest],
    var(FoldPat),
    nonvar(FoldExpr),
    FoldExpr = [foldl, Func, FoldArg, InitExpr],
    FoldArg == Pat, !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(InitExpr, InitConj, InitValue),
    translate_expr_to_conj(Rest, RestConj, RestValue),
    exclude(==(true), [InitConj], VisibleConjs),
    append(GsH, VisibleConjs, MidGoals),
    append(MidGoals,
           [ he_fold_visible_results(ExprConj, ExprVal, Func, InitValue, FoldValue),
             FoldPat = FoldValue,
             RestConj,
             Out = RestValue
           ],
           Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == chain,
    T = [CollapseExpr, Pat, SizeExpr],
    nonvar(CollapseExpr),
    CollapseExpr = [collapse, Expr],
    var(Pat),
    nonvar(SizeExpr),
    SizeExpr = ['size-atom', SizeArg],
    SizeArg == Pat, !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    append(GsH, [he_count_visible_results(ExprConj, ExprVal, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == chain,
    T = [CollapseExpr, Pat, FoldExpr],
    nonvar(CollapseExpr),
    CollapseExpr = [collapse, Expr],
    var(Pat),
    nonvar(FoldExpr),
    FoldExpr = [foldl, Func, FoldArg, InitExpr],
    FoldArg == Pat, !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(InitExpr, InitConj, InitValue),
    exclude(==(true), [InitConj], VisibleConjs),
    append(GsH, VisibleConjs, MidGoals),
    append(MidGoals, [he_fold_visible_results(ExprConj, ExprVal, Func, InitValue, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == chain,
    T = [CollapseExpr, Pat, In],
    nonvar(CollapseExpr),
    CollapseExpr = [collapse, Expr],
    var(Pat),
    nonvar(In),
    In = [let, FoldPat, FoldExpr, Rest],
    var(FoldPat),
    nonvar(FoldExpr),
    FoldExpr = [foldl, Func, FoldArg, InitExpr],
    FoldArg == Pat, !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(InitExpr, InitConj, InitValue),
    translate_expr_to_conj(Rest, RestConj, RestValue),
    exclude(==(true), [InitConj], VisibleConjs),
    append(GsH, VisibleConjs, MidGoals),
    append(MidGoals,
           [ he_fold_visible_results(ExprConj, ExprVal, Func, InitValue, FoldValue),
             FoldPat = FoldValue,
             RestConj,
             Out = RestValue
           ],
           Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == let,
    T = [Pat, Val, In], !,
    he_constrain_args(Pat, Pv, Gp),
    translate_expr_to_conj(Val, ValConj, V),
    translate_expr_to_conj(In, InConj, InValue),
    goals_list_to_conj(Gp, PatConj),
    he_bind_visible_or_cut_goals(GsH, ValConj, V, Pv, PatConj, InConj, InValue, Out, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == chain,
    T = [Val, Pat, In], !,
    he_constrain_args(Pat, Pv, Gp),
    translate_expr_to_conj(Val, ValConj, V),
    translate_expr_to_conj(In, InConj, InValue),
    goals_list_to_conj(Gp, PatConj),
    he_bind_visible_or_cut_goals(GsH, ValConj, V, Pv, PatConj, InConj, InValue, Out, Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertEqual,
    T = [Expr, Expected], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(Expected, ExpConj, ExpVal),
    Goal = ( he_collect_assert_result_sets(ExprConj, ExprVal, ExpConj, ExpVal, Actuals, Expecteds),
             he_assert_set_results([assertEqual, Expr, Expected], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertEqualToResult,
    T = [Expr, ExpectedTuple], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( he_collect_assert_result_tuple(ExprConj, ExprVal, ExpectedTuple, Actuals, Expecteds),
             he_assert_same_results([assertEqualToResult, Expr, ExpectedTuple], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertAlphaEqualToResult,
    T = [Expr, ExpectedTuple], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( he_collect_assert_result_tuple(ExprConj, ExprVal, ExpectedTuple, Actuals, Expecteds),
             he_assert_same_results([assertAlphaEqualToResult, Expr, ExpectedTuple], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertIncludes,
    T = [Expr, ExpectedTuple], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( he_collect_assert_result_tuple(ExprConj, ExprVal, ExpectedTuple, Actuals, Expecteds),
             he_assert_includes_results([assertIncludes, Expr, ExpectedTuple], Actuals, Expecteds, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertEqualMsg,
    T = [Expr, Expected, Msg], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(Expected, ExpConj, ExpVal),
    Goal = ( he_collect_assert_result_set_or_singleton(ExprConj, ExprVal, ExpConj, ExpVal, Actuals, Expecteds),
             he_assert_set_results_or_error([assertEqualMsg, Expr, Expected], Actuals, Expecteds, Msg, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertEqualToResultMsg,
    T = [Expr, ExpectedTuple, Msg], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( he_collect_assert_result_tuple(ExprConj, ExprVal, ExpectedTuple, Actuals, Expecteds),
             he_assert_same_results_or_error([assertEqualToResultMsg, Expr, ExpectedTuple], Actuals, Expecteds, Msg, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertAlphaEqualMsg,
    T = [Expr, Expected, Msg], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr_to_conj(Expected, ExpConj, ExpVal),
    Goal = ( he_collect_assert_result_sets(ExprConj, ExprVal, ExpConj, ExpVal, Actuals, Expecteds),
             he_assert_same_results_or_error([assertAlphaEqualMsg, Expr, Expected], Actuals, Expecteds, Msg, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertAlphaEqualToResultMsg,
    T = [Expr, ExpectedTuple, Msg], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    Goal = ( he_collect_assert_result_tuple(ExprConj, ExprVal, ExpectedTuple, Actuals, Expecteds),
             he_assert_same_results_or_error([assertAlphaEqualToResultMsg, Expr, ExpectedTuple], Actuals, Expecteds, Msg, Out) ),
    append(GsH, [Goal], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == assertPeTTaTest,
    T = [Expr, Expected], !,
    translate_expr_to_conj(Expr, ExprConj, ExprVal),
    translate_expr(Expected, ExpGoals, ExpVal),
    ActualGoal = he_collect_petta_test_actual(ExprVal, ExprConj, ExpVal, Actual),
    AssertGoal = he_assert_petta_test([assertPeTTaTest, Expr, Expected],
                                      Actual, ExpVal, Out),
    append([GsH, ExpGoals, [ActualGoal, AssertGoal]], Goals).

he_translate_match_once_truth_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals) :-
    ( Body == true ; Body == 'True' ),
    translate_expr(SpaceExpr, GsS, S),
    append([GsH, GsS, [he_match_once_truth_empty(S, Pattern, Out)]], Goals).

he_translate_match_once_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals) :-
    ( Body == true ; Body == 'True' ),
    !,
    he_translate_match_once_truth_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals).
he_translate_match_once_empty(SpaceExpr, Pattern, Body, GsH, Out, Goals) :-
    Body == Pattern,
    translate_expr(SpaceExpr, GsS, S),
    append([GsH, GsS, [he_match_once_pattern_empty(S, Pattern, Out)]], Goals).

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
    HV == foldl,
    T = [Func, ListExpr, InitExpr],
    he_profile_enabled,
    nonvar(ListExpr),
    ListExpr = [collapse, ListBody], !,
    translate_expr_to_conj(ListBody, ListConj, ListValue),
    translate_expr_to_conj(InitExpr, InitConj, InitValue),
    exclude(==(true), [InitConj], VisibleConjs),
    append(GsH, VisibleConjs, MidGoals),
    append(MidGoals, [he_fold_visible_results(ListConj, ListValue, Func, InitValue, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == foldl,
    T = [Func, ListExpr, InitExpr], !,
    translate_expr_to_conj(ListExpr, ListConj, ListValue),
    translate_expr_to_conj(InitExpr, InitConj, InitValue),
    exclude(==(true), [ListConj, InitConj], VisibleConjs),
    append(GsH, VisibleConjs, MidGoals),
    append(MidGoals, [he_foldl_reduce(ListValue, Func, InitValue, Out)], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == function,
    T = [Body], !,
    copy_term(Body, SubjectBody),
    translate_expr_to_conj(Body, BodyConj, BodyOut),
    Goal = catch(he_function_body_or_no_return(BodyConj, SubjectBody, BodyOut, Out),
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
    append([GsH, GsS, [he_with_space_snapshot_or_self(Snapshot, SpaceExpr, Space, Body, BodyConj, BodyOut, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == include,
    T = [File], !,
    append([GsH, [he_include_surface('&self', File, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == include,
    T = [SpaceExpr, File], !,
    translate_expr(SpaceExpr, GsS, Space),
    append([GsH, GsS, [he_include_surface(Space, File, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == include, !,
    Out = ['Error', [HV|T], 'IncorrectNumberOfArguments'],
    Goals = GsH.
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == 'import!',
    T = [Space, File], !,
    translate_expr(Space, GsS, S),
    append([GsH, GsS, ['import!'(S, File, Out)]], Goals).
he_translate_special(HV, T, GsH, Out, Goals) :-
    HV == evalc,
    T = [Arg, Space], !,
    translate_expr(Space, GsS, SpaceV),
    append([GsH, GsS, [he_evalc_one(Arg, SpaceV, Out)]], Goals).

he_native_helper_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    atom(HV),
    he_surface(HV, ExpectedArity, native(_), _Scope),
    length(RawArgs, ActualArity),
    ActualArity =\= ExpectedArity,
    !,
    he_display_call_args(HV, RawArgs, DisplayArgs),
    Out = ['Error', [HV|DisplayArgs], 'IncorrectNumberOfArguments'],
    Goals = GsH.
he_native_helper_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    HV == assert,
    RawArgs = [ExprRaw], !,
    translate_expr(ExprRaw, GsExpr, ExprVal),
    append([GsH, GsExpr, [he_native_assert(ExprRaw, ExprVal, Out)]], Goals).
he_native_helper_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    atom(HV),
    memberchk(HV, ['if-equal', 'if-equal2']),
    RawArgs = [LeftRaw, RightRaw, Then, Else], !,
    translate_he_eq_arg(LeftRaw, GsLeft, Left),
    translate_he_eq_arg(RightRaw, GsRight, Right),
    Goal =.. [he_native_if_equal, Left, Right, Then, Else, Out],
    append([GsH, GsLeft, GsRight, [Goal]], Goals).
he_native_helper_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    HV == 'if-error',
    RawArgs = [ExprRaw, Then, Else], !,
    translate_expr(ExprRaw, GsExpr, Expr),
    append([GsH, GsExpr, [he_native_if_error(Expr, Then, Else, Out)]], Goals).
he_native_helper_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    HV == 'return-on-error',
    RawArgs = [ExprRaw, Then], !,
    translate_expr(ExprRaw, GsExpr, Expr),
    append([GsH, GsExpr, [he_native_return_on_error(Expr, Then, Out)]], Goals).
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
    atom(HV),
    he_symbolic_data_functor(HV), !,
    eval_data_list([HV|RawArgs], GsData, Out),
    append(GsH, GsData, Goals).
he_typed_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    atom(HV),
    memberchk(HV, ['==', '!=']),
    RawArgs = [LeftRaw, RightRaw], !,
    translate_he_eq_arg(LeftRaw, GsLeft, Left),
    translate_he_eq_arg(RightRaw, GsRight, Right),
    append([GsH, GsLeft, GsRight, [he_call_typed(HV, [Left, Right], [[->, 'Atom', 'Atom', 'Bool']], Out)]], Goals).
he_typed_dispatch(HV, RawArgs, GsH, Out, Goals) :-
    he_profile_enabled,
    ( atom(HV), Fun = HV, AllRawArgs = RawArgs, PartialMode = direct
    ; compound(HV), HV = partial(Fun, Bound), append(Bound, RawArgs, AllRawArgs), PartialMode = closure
    ),
    he_function_typechains(Fun, TypeChains),
    include(he_arrow_typechain, TypeChains, ArrowTypeChains),
    ArrowTypeChains \= [],
    include(he_typechain_arity_matches(AllRawArgs), ArrowTypeChains, MatchingArity),
    ( MatchingArity == []
    -> ( he_typed_partial_candidate(Fun, PartialMode, AllRawArgs, ArrowTypeChains)
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

he_typed_partial_allowed(_Fun, closure) :- !.
he_typed_partial_allowed('+', direct).
he_typed_partial_allowed('-', direct).
he_typed_partial_allowed('*', direct).
he_typed_partial_allowed('/', direct).
he_typed_partial_allowed('%', direct).
he_typed_partial_allowed(cons, direct).

he_typed_partial_candidate(Fun, PartialMode, Args, TypeChains) :-
    he_typed_partial_allowed(Fun, PartialMode),
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

he_dynamic_head_needs_raw_dispatch(HV) :-
    var(HV), !.
he_dynamic_head_needs_raw_dispatch(HV) :-
    compound(HV),
    HV = partial(_, _).

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

translate_he_eq_arg(A, [], A) :-
    ( var(A)
    ; atomic(A)
    ; is_list(A),
      A = [Head|_],
      atom(Head),
      \+ he_callable_data_head_functor(Head)
    ), !.
translate_he_eq_arg(A, Goals, AV) :-
    translate_expr(A, Goals, AV).

he_arg_stays_data(A, 'Atom') :-
    var(A), !.
he_arg_stays_data(A, 'Atom') :-
    atomic(A), !.
he_arg_stays_data(A, 'Atom') :-
    is_list(A), !.
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
