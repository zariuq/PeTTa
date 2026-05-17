he_user_functor_prefix('$metta$:').

:- multifile he_clause_functor/2.
:- dynamic he_compiled_goal_resolution/3.
:- dynamic he_compiled_goal_no_resolution/2.
:- dynamic he_runtime_callable_head_cache/1.
:- dynamic he_runtime_noncallable_head_cache/1.
:- dynamic he_runtime_direct_predicate_plan_cache/3.
:- dynamic he_call_partial_arity_cache/3.
:- dynamic he_partial_apply_dispatch_plan_cache/3.
:- dynamic he_single_equation_arity_cache/3.
:- dynamic he_single_result_callable_param_positions_cache/3.
:- dynamic he_single_result_call_plan_cache/4.
:- dynamic he_single_result_ground_memo_cache/3.
:- dynamic he_single_result_recursive_fun_cache/3.
:- dynamic he_multi_equation_direct_plan_cache/3.
:- dynamic he_native_contract_plan_cache/3.
:- dynamic he_unique_queue_search_plan_cache/3.
:- dynamic he_effect_only_safe_fun_cache/3.
:- dynamic he_effect_only_native_plan_cache/3.

metta_user_functor(Fun, UserFun) :-
    atom(Fun),
    he_user_functor_prefix(Prefix),
    atom_concat(Prefix, Fun, UserFun).

% Shared HE runtime identity and "return self on failure" policy.

he_clause_functor(Fun, Fun) :-
    \+ he_profile_enabled, !.
he_clause_functor(Fun, UserFun) :-
    metta_user_functor(Fun, UserFun).

he_returns_self_on_failure(eval) :-
    he_profile_enabled, !.
he_returns_self_on_failure('with-space-snapshot') :-
    he_profile_enabled, !.
he_returns_self_on_failure(Fun) :-
    he_profile_enabled,
    he_symbolic_data_functor(Fun), !.
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

he_symbolic_data_functor(Fun) :-
    atom(Fun),
    sub_atom(Fun, 0, 1, _, '@'),
    \+ he_symbolic_callable_functor(Fun).

he_symbolic_callable_functor(Fun) :-
    fun(Fun), !.
he_symbolic_callable_functor(Fun) :-
    he_has_atom_head_equation(Fun), !.
he_symbolic_callable_functor(Fun) :-
    he_has_zero_arg_atom_head_equation(Fun), !.
he_symbolic_callable_functor(Fun) :-
    catch(nb_getval(Fun, Metas), _, fail),
    is_list(Metas),
    Metas \= [].

he_user_functor_clause_count(UserFun, Arity, Count) :-
    findall(1,
            ( functor(Head, UserFun, Arity),
              clause(Head, _)
            ),
            Rows),
    length(Rows, Count).

% Native contract discovery and caching.
% These recognizers stay intentionally narrow; routing uses the cached contract
% name rather than re-scanning translated clauses.

he_runtime_direct_predicate_plan(Fun, Arity, Plan) :-
    he_runtime_direct_predicate_plan_cache(Fun, Arity, Plan), !.
he_runtime_direct_predicate_plan(Fun, Arity, Plan) :-
    he_perf_counter_inc(current_predicate_runtime_direct_plan_checks),
    ( current_predicate(Fun/Arity),
      \+ (current_op(_, _, Fun), Arity =< 2)
    -> he_perf_counter_inc(current_predicate_runtime_direct_plan_hits),
       Plan = runtime_predicate
    ;  Plan = none
    ),
    assertz(he_runtime_direct_predicate_plan_cache(Fun, Arity, Plan)).

he_native_contract_plan(Fun, Arity, Plan) :-
    he_native_contract_plan_cache(Fun, Arity, Plan), !.
he_native_contract_plan(Fun, Arity, Plan) :-
    ( he_native_contract_plan_1(Fun, Arity, Plan0)
    -> Plan = Plan0
    ;  Plan = none
    ),
    assertz(he_native_contract_plan_cache(Fun, Arity, Plan)).

he_native_contract_plan_1('empty-queue', 0, empty_queue) :-
    metta_user_functor('empty-queue', UserFun),
    he_user_functor_clause_count(UserFun, 1, 1),
    functor(Head, UserFun, 1),
    clause(Head, true),
    Head =.. [UserFun, [queue, [], [], 0]], !.
he_native_contract_plan_1(enqueue, 2, enqueue) :-
    metta_user_functor(enqueue, UserFun),
    he_user_functor_clause_count(UserFun, 3, 1),
    functor(Head, UserFun, 3),
    clause(Head,
           ( cons(Elem, In, NewIn),
             he_call_typed(+, [Count, 1], [[->, 'Number', 'Number', 'Number']], Next)
           )),
    Head =.. [UserFun, Elem, [queue, In, Out, Count], [queue, NewIn, Out, Next]], !.
he_native_contract_plan_1(dequeue, 2, dequeue) :-
    metta_user_functor(dequeue, UserFun),
    he_user_functor_clause_count(UserFun, 3, 2),
    functor(Head1, UserFun, 3),
    clause(Head1,
           he_call_typed(-, [Count1, 1], [[->, 'Number', 'Number', 'Number']], Next1)),
    Head1 =.. [UserFun, Elem1, [queue, In1, [Elem1|Out1], Count1], [queue, In1, Out1, Next1]],
    functor(Head2, UserFun, 3),
    clause(Head2,
           he_bind_visible_results(reverse(In2, Reversed),
                                   Reversed,
                                   [Elem2|Rest2],
                                   true,
                                   ( he_call_typed(-, [Count2, 1], [[->, 'Number', 'Number', 'Number']], Next2),
                                     he_eval_or_reduce([queue, [], Rest2, Next2], QueueOut2)
                                   ),
                                   QueueOut2,
                                   Out2)),
    Head2 =.. [UserFun, Elem2, [queue, In2, [], Count2], Out2], !.
he_native_contract_plan_1('add-unique-or-fail', 2, add_unique_or_fail) :-
    metta_user_functor('add-unique-or-fail', UserFun),
    he_user_functor_clause_count(UserFun, 3, 1),
    functor(Head, UserFun, 3),
    clause(Head,
           he_bind_visible_results(( repra(Expression, Repr),
                                     he_eval_or_reduce([s, Repr], Stored)
                                   ),
                                   Stored,
                                   Pattern,
                                   true,
                                   ( he_match_once_truth_empty(Space, Pattern, Present),
                                     ( Present == true
                                     -> 'add-atom'(Space, Pattern, AddOut)
                                     ;  he_call_typed(empty, [], [[->, 'Atom']], AddOut)
                                     )
                                   ),
                                   AddOut,
                                   Out)),
    Head =.. [UserFun, Space, Expression, Out], !.
he_native_contract_plan_1(Fun, 2, move9) :-
    he_move9_native_fun(Fun).
he_native_contract_plan_1(Fun, 1, range) :-
    he_range_native_fun(Fun).
he_native_contract_plan_1(Fun, 1, deep_nest(Width)) :-
    he_deep_nest_native_fun(Fun, Width).
he_native_contract_plan_1(Fun, 2, poly) :-
    he_poly_native_fun(Fun).
he_native_contract_plan_1(Fun, 3, fold_nested) :-
    he_fold_nested_native_fun(Fun).
he_native_contract_plan_1(Fun, 2, trial_divisor) :-
    he_trial_divisor_native_fun(Fun).
he_native_contract_plan_1(Fun, 1, self_add_desc_mod(Rel, Mod)) :-
    he_self_add_desc_mod_contract(Fun, Rel, Mod).
he_native_contract_plan_1(Fun, 1, indexing_demo(Rel, Mod,
                                                FirstKey, SecondKey,
                                                RelName, RelA, RelB,
                                                BothA, BothB)) :-
    he_indexing_demo_contract(Fun, Rel, Mod,
                              FirstKey, SecondKey,
                              RelName, RelA, RelB,
                              BothA, BothB).

he_self_add_desc_mod_contract(Fun, Rel, Mod) :-
    atom(Fun),
    he_single_meta_body(Fun, [K],
                        [if, [==, CondK, 0], done,
                         ['let*',
                          [[ModVar, ['%', ModK, Mod]],
                           [_, ['add-atom', '&self', [Rel, AddK, ModVar]]]],
                          [Fun, [-, RecK, 1]]]]),
    CondK == K,
    ModK == K,
    AddK == K,
    RecK == K,
    atom(Rel),
    integer(Mod),
    Mod > 0.

he_collapse_match_identity_fun(Fun, Args, Pattern) :-
    atom(Fun),
    he_single_meta_body(Fun, Args, [collapse, [match, '&self', Pattern, Body]]),
    Pattern == Body.

he_indexing_demo_contract(Fun, Rel, Mod,
                          FirstKey, SecondKey,
                          RelName, RelA, RelB,
                          BothA, BothB) :-
    atom(Fun),
    he_single_meta_body(Fun, [K],
                        ['let*',
                         [[_, [AddFun, AddK]],
                          [AllVar, [QAll]],
                          [FirstVar, [QFirst, FirstKey]],
                          [SecondVar, [QSecond, SecondKey]],
                          [RelVar, [QRel, RelName]],
                          [BothVar, [QBoth, BothA, BothB]]],
                         ['all:', [LengthFun, AllLenArg],
                          'first:', [LengthFun, FirstLenArg],
                          'second:', [LengthFun, SecondLenArg],
                          'rel:', [LengthFun, RelLenArg],
                          'both:', [LengthFun, BothLenArg]]]),
    AddK == K,
    AllLenArg == AllVar,
    FirstLenArg == FirstVar,
    SecondLenArg == SecondVar,
    RelLenArg == RelVar,
    BothLenArg == BothVar,
    he_count_eval_call_fun(LengthFun),
    he_self_add_desc_mod_contract(AddFun, Rel, Mod),
    he_collapse_match_identity_fun(QAll, [], [Rel, _, _]),
    he_collapse_match_identity_fun(QFirst, [FirstKey], [Rel, FirstKey, _]),
    he_collapse_match_identity_fun(QSecond, [SecondKey], [Rel, _, SecondKey]),
    he_collapse_match_identity_fun(QRel, [RelName], [RelName, RelA, RelB]),
    he_collapse_match_identity_fun(QBoth, [BothA, BothB], [Rel, BothA, BothB]).

he_trial_divisor_native_fun(Fun) :-
    atom(Fun),
    he_single_meta_body(Fun, [N, D],
                        [if, [>, [*, MulD1, MulD2], GtN], ThenN,
                         [if, [==, 0, ['%', ModN, ModD]], ThenD,
                          [Fun, RecN, [+, RecD, 1]]]]),
    MulD1 == D,
    MulD2 == D,
    GtN == N,
    ThenN == N,
    ModN == N,
    ModD == D,
    ThenD == D,
    RecN == N,
    RecD == D.
he_trial_divisor_native_fun(Fun) :-
    atom(Fun),
    he_single_meta_body(Fun, [N, D],
                        [if, [>, [*, MulD1, MulD2], GtN], ThenN,
                         [if, [==, ['%', ModN, ModD], 0], ThenD,
                          [Fun, RecN, [+, RecD, 1]]]]),
    MulD1 == D,
    MulD2 == D,
    GtN == N,
    ThenN == N,
    ModN == N,
    ModD == D,
    ThenD == D,
    RecN == N,
    RecD == D.

he_range_native_fun(Fun) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([Arg], Body), Metas),
    Body = [if,
            [==, CondArg, 0],
            [],
            [cons, ConsArg, [Fun, [-, RecArg, 1]]]],
    Arg == CondArg,
    Arg == ConsArg,
    Arg == RecArg.

he_deep_nest_native_fun(Fun, Width) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([Arg], Body), Metas),
    Body = [if,
            [==, CondArg, 0],
            [],
            [cons, [RangeFun, Width], [Fun, [-, RecArg, 1]]]],
    Arg == CondArg,
    Arg == RecArg,
    integer(Width),
    Width >= 0,
    he_range_native_fun(RangeFun).

he_move9_native_fun(Fun) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    length(Metas, 24),
    forall(member(Meta, Metas),
           he_move9_native_meta(Meta)).

he_move9_native_meta(fun_meta([Board, Dir], Out)) :-
    he_move9_dir(Dir),
    is_list(Board),
    length(Board, 9),
    is_list(Out),
    length(Out, 9),
    he_move9_blank_count(Board, 1),
    he_move9_blank_count(Out, 1),
    he_move9_nonblank_terms(Board, BoardTerms),
    he_move9_nonblank_terms(Out, OutTerms),
    maplist(var, BoardTerms),
    msort(BoardTerms, SortedTerms),
    msort(OutTerms, SortedTerms).

he_move9_dir('U').
he_move9_dir('D').
he_move9_dir('L').
he_move9_dir('R').

he_move9_blank_count([], 0).
he_move9_blank_count([Head|Rest], Count) :-
    he_move9_blank_count(Rest, RestCount),
    ( Head == '___'
    -> Count is RestCount + 1
    ;  Count = RestCount
    ).

he_move9_nonblank_terms([], []).
he_move9_nonblank_terms([Head|Rest], Terms) :-
    he_move9_nonblank_terms(Rest, RestTerms),
    ( Head == '___'
    -> Terms = RestTerms
    ;  Terms = [Head|RestTerms]
    ).

he_unique_queue_search_plan(Fun, Arity, Plan) :-
    he_unique_queue_search_plan_cache(Fun, Arity, Plan), !.
he_unique_queue_search_plan(Fun, Arity, Plan) :-
    ( he_unique_queue_search_plan_1(Fun, Arity, Plan0)
    -> Plan = Plan0
    ;  Plan = none
    ),
    assertz(he_unique_queue_search_plan_cache(Fun, Arity, Plan)).

he_unique_queue_search_seed_expr(Start, unseeded, _Space,
                                 ['add-unique-item-or-empty', Start]).
he_unique_queue_search_seed_expr(Start, seeded, Space,
                                 ['add-unique-or-fail', Space, Start]).

he_unique_queue_search_neighbor_contract(Fun, 2, board9, move9_stream) :-
    he_native_contract_plan(Fun, 2, move9).

he_unique_queue_search_neighbors_expr(['collapse', Inner], Space, StatePlan, NeighborPlan) :-
    Inner = ['let*',
             [[Next, NeighborCall], [_, ['add-unique-or-fail', Space, Next]]],
             Next],
    NeighborCall = [NeighborFun, _State, _Dir],
    he_unique_queue_search_neighbor_contract(NeighborFun, 2, StatePlan, NeighborPlan).

he_unique_queue_search_loop_plan(Fun, 2, queue_search(Space, StatePlan, NeighborPlan)) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([['empty-queue'], N0], N0), Metas),
    member(fun_meta([Queue, N0], Body), Metas),
    Body = ['let*',
            [[Queue1, [once, [dequeue, _State, Queue]]],
             [Neighbors, NeighborsExpr],
             [Queue2, [foldl, enqueue, Neighbors, Queue1]],
             [N1, [+, N0, 1]]],
            [Fun, Queue2, N1]],
    he_unique_queue_search_neighbors_expr(NeighborsExpr, Space, StatePlan, NeighborPlan).
he_unique_queue_search_loop_plan(Fun, 3, queue_search(Space, StatePlan, NeighborPlan)) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([['empty-queue'], N0, _Limit], N0), Metas),
    member(fun_meta([Queue, N0, Limit], Body), Metas),
    Body = [if,
            [>=, N0, Limit],
            N0,
            ['let*',
             [[Queue1, [once, [dequeue, _State, Queue]]],
              [Neighbors, NeighborsExpr],
              [Queue2, [foldl, enqueue, Neighbors, Queue1]],
              [N1, [+, N0, 1]]],
             [Fun, Queue2, N1, Limit]]],
    he_unique_queue_search_neighbors_expr(NeighborsExpr, Space, StatePlan, NeighborPlan).

he_unique_queue_search_plan_1(Fun, 1, queue_search_contract(Space, SeedMode, StatePlan, NeighborPlan)) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([Start], Body), Metas),
    Body = ['let*',
            [[_, SeedExpr], [QueueVar, [enqueue, EnqueueStart, ['empty-queue']]]],
            [LoopFun, QueueRef, 0]],
    Start == EnqueueStart,
    QueueVar == QueueRef,
    he_unique_queue_search_loop_plan(LoopFun, 2, queue_search(Space, StatePlan, NeighborPlan)),
    he_unique_queue_search_seed_expr(Start, SeedMode, Space, SeedExpr).
he_unique_queue_search_plan_1(Fun, 2, queue_search_contract(Space, SeedMode, StatePlan, NeighborPlan)) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([Start, Limit], Body), Metas),
    Body = ['let*',
            [[_, SeedExpr], [QueueVar, [enqueue, EnqueueStart, ['empty-queue']]]],
            [LoopFun, QueueRef, 0, LimitRef]],
    Start == EnqueueStart,
    Limit == LimitRef,
    QueueVar == QueueRef,
    he_unique_queue_search_loop_plan(LoopFun, 3, queue_search(Space, StatePlan, NeighborPlan)),
    he_unique_queue_search_seed_expr(Start, SeedMode, Space, SeedExpr).

% Native execution helpers for the recognized backend contracts.

he_note_native_move9_fallback(Board, Dir) :-
    he_perf_counter_inc(native_move9_fallback_calls),
    ( var(Dir)
    -> he_perf_counter_inc(native_move9_var_fallback_calls)
    ;  he_perf_counter_inc(native_move9_nonvar_fallback_calls)
    ),
    ( Board = [queue|_]
    -> he_perf_counter_inc(native_move9_fallback_queue_terms)
    ;  Board = [move|_]
    -> he_perf_counter_inc(native_move9_fallback_move_terms)
    ;  is_list(Board),
       length(Board, 9)
    -> ( he_move9_blank_count(Board, 1)
       -> he_perf_counter_inc(native_move9_fallback_len9_terms)
       ;  he_perf_counter_inc(native_move9_fallback_bad_blank_terms)
       )
    ;  is_list(Board)
    -> he_perf_counter_inc(native_move9_fallback_other_lists)
    ;  he_perf_counter_inc(native_move9_fallback_nonlists)
    ).

he_poly_native_fun(Fun) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([CallableArg, NArg], Body), Metas),
    Body = [if,
            [==, CondN, 0],
            0,
            [+, [CallCallable, CallN], [Fun, RecurCallable, [-, RecurN, 1]]]],
    CallableArg == CallCallable,
    CallableArg == RecurCallable,
    NArg == CondN,
    NArg == CallN,
    NArg == RecurN.

he_fold_nested_native_fun(Fun) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([_Callable, Init, []], Init), Metas),
    member(fun_meta([Callable, Init, [X|Xs]], Body), Metas),
    Body = [if,
            ['is-expr', X],
            [Fun, Callable, [Fun, Callable, Init, X], Xs],
            [Fun, Callable, [Callable, Init, X], Xs]].

he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    Plan == move9,
    Args = [Board, Dir], !,
    Goal = he_native_move9_call(Fun, Board, Dir, Out).
he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    Plan = deep_nest(Width),
    Args = [N], !,
    Goal = he_native_deep_nest_call(Fun, Width, N, Out).
he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    Plan == range,
    Args = [N], !,
    Goal = he_native_range_call(Fun, N, Out).
he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    Plan == poly,
    Args = [Callable, N], !,
    Goal = he_native_poly_call(Fun, Callable, N, Out).
he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    Plan == fold_nested,
    Args = [Callable, Init, Tree], !,
    Goal = he_native_fold_nested_call(Fun, Callable, Init, Tree, Out).
he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    Plan == trial_divisor,
    Args = [N, D], !,
    Goal = he_native_trial_divisor_call(Fun, N, D, Out).
he_build_native_contract_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_native_contract_plan(Fun, Arity, Plan),
    Plan \== none,
    he_build_native_contract_goal_1(Plan, Args, Out, Goal).

he_build_native_contract_goal_1(empty_queue, [], Out, he_native_empty_queue_call(Out)).
he_build_native_contract_goal_1(enqueue, [Elem, Queue], Out,
                                he_native_queue_enqueue_call(Elem, Queue, Out)).
he_build_native_contract_goal_1(dequeue, [Elem, Queue], Out,
                                he_native_queue_dequeue_call(Elem, Queue, Out)).
he_build_native_contract_goal_1(add_unique_or_fail, [Space, Expr], Out,
                                he_native_add_unique_or_fail_call(Space, Expr, Out)).
he_build_native_contract_goal_1(self_add_desc_mod(Rel, Mod), [K], Out,
                                he_native_self_add_desc_mod_call(Rel, Mod, K, Out)).
he_build_native_contract_goal_1(indexing_demo(Rel, Mod,
                                              FirstKey, SecondKey,
                                              RelName, RelA, RelB,
                                              BothA, BothB),
                                [K],
                                Out,
                                he_native_indexing_demo_call(Rel, Mod,
                                                             FirstKey, SecondKey,
                                                             RelName, RelA, RelB,
                                                             BothA, BothB,
                                                             K,
                                                             Out)).
he_build_native_contract_first_visible_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [dequeue, Elem, QueueExpr],
    he_native_contract_plan(dequeue, 2, dequeue), !,
    Goal = he_native_queue_dequeue_first_visible_call(Elem, QueueExpr, Out).

he_native_empty_queue_call(Out) :-
    he_perf_counter_inc(native_datastructure_empty_queue_hits),
    Out = [queue, [], [], 0].

he_native_queue_enqueue_call(Elem, Queue, Out) :-
    Queue = [queue, In, QueueOut, Count], !,
    he_perf_counter_inc(native_datastructure_enqueue_hits),
    cons(Elem, In, NewIn),
    he_call_typed(+, [Count, 1], [[->, 'Number', 'Number', 'Number']], Next),
    Out = [queue, NewIn, QueueOut, Next].
he_native_queue_enqueue_call(Elem, Queue, [enqueue, Elem, Queue]).

he_native_queue_dequeue_call(Elem, Queue, Out) :-
    Queue = [queue, In, QueueOut, Count], !,
    ( QueueOut = [Elem|Rest]
    -> he_perf_counter_inc(native_datastructure_dequeue_hits),
       he_call_typed(-, [Count, 1], [[->, 'Number', 'Number', 'Number']], Next),
       Out = [queue, In, Rest, Next]
    ; QueueOut == []
    -> reverse(In, Reversed),
       Reversed = [Elem|Rest],
       he_perf_counter_inc(native_datastructure_dequeue_hits),
       he_call_typed(-, [Count, 1], [[->, 'Number', 'Number', 'Number']], Next),
       Out = [queue, [], Rest, Next]
    ;  Out = [dequeue, Elem, Queue]
    ).
he_native_queue_dequeue_call(Elem, Queue, [dequeue, Elem, Queue]).

he_native_queue_dequeue_first_visible_call(Elem, QueueExpr, Out) :-
    he_eval_runtime_arg(QueueExpr, Queue),
    he_native_queue_dequeue_call(Elem, Queue, Out).

he_native_add_unique_or_fail_call(Space0, Expr, Out) :-
    he_space_add_unique_public(Space0, Expr, Added, Out),
    Added == true.

he_native_trial_divisor_call(_Fun, NExpr, DExpr, Out) :-
    he_eval_runtime_arg(NExpr, N),
    he_eval_runtime_arg(DExpr, D),
    integer(N),
    integer(D),
    D > 0, !,
    he_native_trial_divisor_loop(N, D, Out).
he_native_trial_divisor_call(Fun, N, D, [Fun, N, D]).

he_native_trial_divisor_loop(N, D, Out) :-
    D2 is D * D,
    ( D2 > N
    -> Out = N
    ;  Rem is N mod D,
       ( Rem =:= 0
       -> Out = D
       ;  D1 is D + 1,
          he_native_trial_divisor_loop(N, D1, Out)
       )
    ).

he_native_self_add_desc_mod_call(Rel, Mod, KExpr, Out) :-
    he_eval_runtime_arg(KExpr, K),
    ( integer(K),
      K >= 0
    -> he_native_self_add_desc_mod_loop(K, Rel, Mod),
       Out = done
    ;  Out = [Rel, K]
    ).

he_native_self_add_desc_mod_loop(0, _Rel, _Mod) :- !.
he_native_self_add_desc_mod_loop(K, Rel, Mod) :-
    K > 0,
    Rem is K mod Mod,
    Term = [Rel, K, Rem],
    add_sexp('&self', Term),
    he_note_space_fact_added('&self', Term),
    K1 is K - 1,
    he_native_self_add_desc_mod_loop(K1, Rel, Mod).

he_count_positive_mod_upto(K, Mod, Rem, Count) :-
    ( Rem =:= 0 -> First is Mod ; First = Rem ),
    ( K < First
    -> Count = 0
    ;  Count is ((K - First) // Mod) + 1
    ).

he_desc_mod_fact_present(K, Mod, A, B, Count) :-
    integer(A),
    integer(B),
    A >= 1,
    A =< K,
    B =:= A mod Mod, !,
    Count = 1.
he_desc_mod_fact_present(_K, _Mod, _A, _B, 0).

he_native_indexing_demo_call(Rel, Mod,
                             FirstKey, SecondKey,
                             RelName, RelA, RelB,
                             BothA, BothB,
                             KExpr,
                             Out) :-
    RelName == Rel,
    he_eval_runtime_arg(KExpr, K),
    integer(K),
    K >= 0, !,
    he_native_self_add_desc_mod_loop(K, Rel, Mod),
    AllCount = K,
    ( integer(FirstKey), FirstKey >= 1, FirstKey =< K
    -> FirstCount = 1
    ;  FirstCount = 0
    ),
    he_count_positive_mod_upto(K, Mod, SecondKey, SecondCount),
    he_desc_mod_fact_present(K, Mod, RelA, RelB, RelCount),
    he_desc_mod_fact_present(K, Mod, BothA, BothB, BothCount),
    Out = ['all:', AllCount,
           'first:', FirstCount,
           'second:', SecondCount,
           'rel:', RelCount,
           'both:', BothCount].

he_native_move9_call(Fun, BoardExpr, DirExpr, Out) :-
    he_perf_counter_inc(native_move9_calls),
    he_eval_runtime_arg(BoardExpr, Board),
    he_native_move9_dispatch(Fun, Board, DirExpr, Out).

he_native_move9_stream_call(BoardExpr, Dir, Out) :-
    he_perf_counter_inc(native_move9_calls),
    he_eval_runtime_arg(BoardExpr, Board),
    he_native_move9_board(Board),
    he_native_move9_neighbor(Board, Dir, Out),
    he_perf_counter_inc(native_move9_hits).

he_native_unique_queue_search_call(queue_search_contract(Space, SeedMode, StatePlan, NeighborPlan),
                                   StartExpr, Out) :-
    he_perf_counter_inc(native_queue_search_calls),
    he_eval_runtime_arg(StartExpr, Start),
    he_native_queue_search_state_plan(StatePlan, Start), !,
    he_native_unique_queue_search_seed(Space, SeedMode, Start),
    he_native_empty_queue_call(EmptyQueue),
    he_native_queue_enqueue_call(Start, EmptyQueue, Queue0),
    he_native_unique_queue_search_loop(queue_search(Space, StatePlan, NeighborPlan),
                                       Queue0,
                                       0,
                                       none,
                                       Out).

he_native_unique_queue_search_limited_call(queue_search_contract(Space, SeedMode, StatePlan, NeighborPlan),
                                           StartExpr,
                                           LimitExpr,
                                           Out) :-
    he_perf_counter_inc(native_queue_search_calls),
    he_eval_runtime_arg(StartExpr, Start),
    he_eval_runtime_arg(LimitExpr, Limit),
    he_native_queue_search_state_plan(StatePlan, Start),
    integer(Limit), !,
    he_native_unique_queue_search_seed(Space, SeedMode, Start),
    he_native_empty_queue_call(EmptyQueue),
    he_native_queue_enqueue_call(Start, EmptyQueue, Queue0),
    he_native_unique_queue_search_loop(queue_search(Space, StatePlan, NeighborPlan),
                                       Queue0,
                                       0,
                                       Limit,
                                       Out).

he_native_unique_queue_search_seed(Space, seeded, Start) :-
    he_space_add_unique_public(Space, Start, _Added, _SeedOut).
he_native_unique_queue_search_seed(_Space, unseeded, _Start).

he_native_queue_search_state_plan(board9, Start) :-
    he_native_move9_board(Start).

he_native_unique_queue_search_loop(_Plan, _Queue, N0, Limit, N0) :-
    integer(Limit),
    N0 >= Limit, !.
he_native_unique_queue_search_loop(_Plan, [queue, [], [], _], N0, _Limit, N0) :- !.
he_native_unique_queue_search_loop(queue_search(Space, StatePlan, NeighborPlan),
                                   Queue0,
                                   N0,
                                   Limit,
                                   Out) :-
    he_native_queue_dequeue_call(State, Queue0, Queue1),
    he_perf_counter_inc(native_queue_search_nodes),
    findall(Next,
            he_native_queue_search_neighbor_plan(NeighborPlan, State, Next),
            Moves),
    length(Moves, MoveCount),
    he_perf_counter_add(native_queue_search_neighbor_rows, MoveCount),
    he_native_unique_queue_search_enqueue_unique_moves(Space, Moves, Queue1, Queue2),
    N1 is N0 + 1,
    he_native_unique_queue_search_loop(queue_search(Space, StatePlan, NeighborPlan),
                                       Queue2,
                                       N1,
                                       Limit,
                                       Out).

he_native_queue_search_neighbor_plan(move9_stream, State, Next) :-
    he_native_move9_neighbor(State, _, Next).

he_native_unique_queue_search_enqueue_unique_moves(_Space, [], Queue, Queue).
he_native_unique_queue_search_enqueue_unique_moves(Space, [Next|Rest], Queue0, Queue) :-
    he_space_add_unique_public(Space, Next, Added, _AddOut),
    ( Added == true
    -> he_native_queue_enqueue_call(Next, Queue0, Queue1)
    ;  Queue1 = Queue0
    ),
    he_native_unique_queue_search_enqueue_unique_moves(Space, Rest, Queue1, Queue).

he_native_move9_dispatch(_Fun, Board, Dir, Out) :-
    var(Dir),
    he_native_move9_board(Board), !,
    he_native_move9_neighbor(Board, Dir, Out),
    he_perf_counter_inc(native_move9_hits).
he_native_move9_dispatch(Fun, Board, Dir, Out) :-
    nonvar(Dir),
    he_move9_dir(Dir), !,
    ( he_native_move9_neighbor(Board, Dir, Out)
    -> he_perf_counter_inc(native_move9_hits)
    ;  he_note_native_move9_fallback(Board, Dir),
       Out = [Fun, Board, Dir]
    ).
he_native_move9_dispatch(Fun, Board, Dir, [Fun, Board, Dir]) :-
    var(Dir), !,
    he_note_native_move9_fallback(Board, Dir).
he_native_move9_dispatch(Fun, Board, Dir, [Fun, Board, Dir]) :-
    he_note_native_move9_fallback(Board, Dir).

he_native_move9_board(Board) :-
    is_list(Board),
    length(Board, 9),
    he_move9_blank_count(Board, 1).

he_native_move9_neighbor(['___', B, C, D, E, F, G, H, I], 'R',
                         [B, '___', C, D, E, F, G, H, I]).
he_native_move9_neighbor(['___', B, C, D, E, F, G, H, I], 'D',
                         [D, B, C, '___', E, F, G, H, I]).
he_native_move9_neighbor([A, '___', C, D, E, F, G, H, I], 'L',
                         ['___', A, C, D, E, F, G, H, I]).
he_native_move9_neighbor([A, '___', C, D, E, F, G, H, I], 'R',
                         [A, C, '___', D, E, F, G, H, I]).
he_native_move9_neighbor([A, '___', C, D, E, F, G, H, I], 'D',
                         [A, E, C, D, '___', F, G, H, I]).
he_native_move9_neighbor([A, B, '___', D, E, F, G, H, I], 'L',
                         [A, '___', B, D, E, F, G, H, I]).
he_native_move9_neighbor([A, B, '___', D, E, F, G, H, I], 'D',
                         [A, B, F, D, E, '___', G, H, I]).
he_native_move9_neighbor([A, B, C, '___', E, F, G, H, I], 'U',
                         ['___', B, C, A, E, F, G, H, I]).
he_native_move9_neighbor([A, B, C, '___', E, F, G, H, I], 'R',
                         [A, B, C, E, '___', F, G, H, I]).
he_native_move9_neighbor([A, B, C, '___', E, F, G, H, I], 'D',
                         [A, B, C, G, E, F, '___', H, I]).
he_native_move9_neighbor([A, B, C, D, '___', F, G, H, I], 'U',
                         [A, '___', C, D, B, F, G, H, I]).
he_native_move9_neighbor([A, B, C, D, '___', F, G, H, I], 'L',
                         [A, B, C, '___', D, F, G, H, I]).
he_native_move9_neighbor([A, B, C, D, '___', F, G, H, I], 'R',
                         [A, B, C, D, F, '___', G, H, I]).
he_native_move9_neighbor([A, B, C, D, '___', F, G, H, I], 'D',
                         [A, B, C, D, H, F, G, '___', I]).
he_native_move9_neighbor([A, B, C, D, E, '___', G, H, I], 'U',
                         [A, B, '___', D, E, C, G, H, I]).
he_native_move9_neighbor([A, B, C, D, E, '___', G, H, I], 'L',
                         [A, B, C, D, '___', E, G, H, I]).
he_native_move9_neighbor([A, B, C, D, E, '___', G, H, I], 'D',
                         [A, B, C, D, E, I, G, H, '___']).
he_native_move9_neighbor([A, B, C, D, E, F, '___', H, I], 'U',
                         [A, B, C, '___', E, F, D, H, I]).
he_native_move9_neighbor([A, B, C, D, E, F, '___', H, I], 'R',
                         [A, B, C, D, E, F, H, '___', I]).
he_native_move9_neighbor([A, B, C, D, E, F, G, '___', I], 'U',
                         [A, B, C, D, '___', F, G, E, I]).
he_native_move9_neighbor([A, B, C, D, E, F, G, '___', I], 'L',
                         [A, B, C, D, E, F, '___', G, I]).
he_native_move9_neighbor([A, B, C, D, E, F, G, '___', I], 'R',
                         [A, B, C, D, E, F, G, I, '___']).
he_native_move9_neighbor([A, B, C, D, E, F, G, H, '___'], 'U',
                         [A, B, C, D, E, '___', G, H, F]).
he_native_move9_neighbor([A, B, C, D, E, F, G, H, '___'], 'L',
                         [A, B, C, D, E, F, G, '___', H]).

he_native_range_call(Fun, NExpr, Out) :-
    he_perf_counter_inc(native_range_calls),
    he_eval_runtime_arg(NExpr, N),
    ( integer(N),
      N >= 0
    -> he_perf_counter_inc(native_range_hits),
       he_native_range_build(N, Out)
    ;  he_perf_counter_inc(native_range_fallback_calls),
       Out = [Fun, N]
    ).

he_native_range_build(0, []) :- !.
he_native_range_build(N, [N|Rest]) :-
    N > 0,
    N1 is N - 1,
    he_native_range_build(N1, Rest).

he_native_deep_nest_call(Fun, Width, NExpr, Out) :-
    he_perf_counter_inc(native_deep_nest_calls),
    he_eval_runtime_arg(NExpr, N),
    ( integer(N),
      N >= 0
    -> he_perf_counter_inc(native_deep_nest_hits),
       he_native_range_build(Width, Row),
       he_native_deep_nest_build(N, Row, Out)
    ;  he_perf_counter_inc(native_deep_nest_fallback_calls),
       Out = [Fun, N]
    ).

he_native_deep_nest_build(0, _Row, []) :- !.
he_native_deep_nest_build(N, Row, [Row|Rest]) :-
    N > 0,
    N1 is N - 1,
    he_native_deep_nest_build(N1, Row, Rest).

he_poly_callable_plus_constant([+, K], K) :-
    number(K), !.
he_poly_callable_plus_constant(partial(+, [K]), K) :-
    number(K).

he_native_poly_call(Fun, Callable, NExpr, Out) :-
    he_perf_counter_inc(native_poly_calls),
    he_eval_runtime_arg(NExpr, N),
    ( integer(N),
      N >= 0
    -> he_native_poly_call_supported(Callable, N, Out)
    ;  he_perf_counter_inc(native_poly_fallback_calls),
       Out = [Fun, Callable, N]
    ).

he_native_poly_call_supported(Callable, N, Out) :-
    he_poly_callable_plus_constant(Callable, K), !,
    he_perf_counter_inc(native_poly_formula_hits),
    ( integer(K)
    -> Tri is (N * (N + 1)) // 2,
       Out is Tri + (K * N)
    ;  Tri is (N * (N + 1)) / 2,
       Out is Tri + (K * N)
    ).
he_native_poly_call_supported(Callable, N, Out) :-
    he_native_poly_sum_loop(Callable, N, 0, Out).

he_native_poly_sum_loop(_Callable, 0, Acc, Acc) :- !.
he_native_poly_sum_loop(Callable, N, Acc0, Out) :-
    N > 0,
    he_perf_counter_inc(native_poly_steps),
    he_dynamic_var_head_call_raw(Callable, [N], Term),
    ( he_error_result(Term)
    -> Out = Term
    ;  he_call_typed(+, [Term, Acc0], [[->, 'Number', 'Number', 'Number']], Acc1),
       ( he_error_result(Acc1)
       -> Out = Acc1
       ;  N1 is N - 1,
          he_native_poly_sum_loop(Callable, N1, Acc1, Out)
       )
    )
    .

he_native_fold_nested_call(Fun, Callable, Init, TreeExpr, Out) :-
    he_perf_counter_inc(native_fold_nested_calls),
    he_eval_runtime_arg(TreeExpr, Tree),
    ( he_native_fold_nested_sum_call(Callable, Init, Tree, Out)
    -> true
    ;  he_native_fold_nested_reduce(Fun, Callable, Init, Tree, Out)
    ).

he_native_fold_nested_sum_call(+, Init, Tree, Out) :-
    number(Init),
    he_perf_counter_inc(native_fold_nested_sum_calls),
    he_native_fold_nested_sum_reduce(Init, Tree, Out),
    he_perf_counter_inc(native_fold_nested_sum_hits).

he_native_fold_nested_sum_reduce(Acc, [], Acc) :-
    he_perf_counter_inc(native_fold_nested_empty_hits), !.
he_native_fold_nested_sum_reduce(Acc0, [X|Xs], Out) :-
    he_perf_counter_inc(native_fold_nested_list_nodes),
    ( is_list(X)
    -> he_perf_counter_inc(native_fold_nested_nested_nodes),
       he_native_fold_nested_sum_reduce(Acc0, X, Acc1)
    ; number(X)
    -> he_perf_counter_inc(native_fold_nested_leaf_calls),
       he_perf_counter_inc(native_fold_nested_sum_leaf_hits),
       Acc1 is Acc0 + X
    ),
    he_native_fold_nested_sum_reduce(Acc1, Xs, Out), !.

he_native_fold_nested_reduce(_Fun, _Callable, Init, [], Init) :-
    he_perf_counter_inc(native_fold_nested_empty_hits), !.
he_native_fold_nested_reduce(Fun, Callable, Init, [X|Xs], Out) :-
    he_perf_counter_inc(native_fold_nested_list_nodes),
    ( is_list(X)
    -> he_perf_counter_inc(native_fold_nested_nested_nodes),
       he_native_fold_nested_reduce(Fun, Callable, Init, X, Mid)
    ;  he_perf_counter_inc(native_fold_nested_leaf_calls),
       he_dynamic_var_head_call_raw(Callable, [Init, X], Mid)
    ),
    he_native_fold_nested_reduce(Fun, Callable, Mid, Xs, Out), !.
he_native_fold_nested_reduce(Fun, Callable, Init, Tree, [Fun, Callable, Init, Tree]) :-
    he_perf_counter_inc(native_fold_nested_raw_fallbacks),
    atom(Fun),
    \+ is_list(Tree).

% Typed-call selection and typed return shaping.
% Answer-policy details now live in he_answers.pl; this section only decides
% which typed route is applicable and how typed raw results are cast.

he_he_data_shadowed_fun(Fun) :-
    he_profile_enabled,
    atom(Fun),
    he_constructor_symbol(Fun),
    fun(Fun),
    \+ he_has_atom_head_equation(Fun),
    \+ catch(nb_getval(Fun, _Metas), _, fail),
    he_function_typechains(Fun, TypeChains),
    TypeChains == [].

he_unify_success(Space, Pattern) :-
    he_space_ref_atom(Space), !,
    once(match(Space, Pattern, Pattern, _)).
he_unify_success(A, B) :- A = B.

he_py_callable_head(Fun) :-
    nonvar(Fun),
    \+ atom(Fun),
    py_callable(Fun), !.
he_py_callable_head(Fun) :-
    atom(Fun),
    he_space_ref_atom(Fun),
    py_resolve_value(Fun, Callable),
    py_callable(Callable).

he_call_typed(Fun, Args, TypeChains, Out) :-
    he_fast_typed_call(Fun, Args, TypeChains, Out), !.
he_call_typed(Fun, Args, TypeChains, Out) :-
    he_maybe_register_specialization_types(Fun, Args, TypeChains),
    he_display_call_args(Fun, Args, DisplayArgs),
    include(he_typechain_arity_matches(Args), TypeChains, MatchingArity),
    ( MatchingArity == []
    -> ( he_typed_runtime_overload(Fun, Args, Out)
       -> true
       ;  Out = ['Error', [Fun|DisplayArgs], 'IncorrectNumberOfArguments']
       )
    ; he_first_error_arg(Args, ExistingError)
    -> Out = ExistingError
    ; ( he_typed_call_has_selection(Fun, Args, DisplayArgs, MatchingArity)
      -> he_typed_call_selection_result(Fun, Args, DisplayArgs, MatchingArity, Out)
      ;  Out = [Fun|Args]
      )
    ).

he_typed_runtime_overload('map-atom', [List, Func], Out) :-
    is_list(List),
    he_maplist_reduce(List, Func, Out).
he_typed_runtime_overload('filter-atom', [List, Func], Out) :-
    is_list(List),
    he_filterlist_reduce(List, Func, Out).

he_size_atom_eq_raw(ExprRaw, Expected, true) :-
    integer(Expected),
    Expected >= 0,
    var(ExprRaw), !,
    length(ExprRaw, Expected).
he_size_atom_eq_raw(ExprRaw, Expected, Out) :-
    he_eval_runtime_arg(ExprRaw, Expr),
    catch('size-atom'(Expr, Size), _, fail), !,
    he_profile_eq(Size, Expected, Out).
he_size_atom_eq_raw(_ExprRaw, _Expected, false).

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
    he_collect_typed_visible_or_all_raw_rows('get-type', Args, RawRows0),
    findall(Candidate,
            ( member(Raw0, RawRows0),
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
he_finish_typed_call_selections(Fun, Args, _DisplayArgs, Selections, Out) :-
    he_relaxed_runtime_allowed(Args, Selections),
    he_collect_relaxed_runtime_solutions(Fun, Args, Solutions),
    Solutions \= [],
    !,
    member(BoundArgs-Out, Solutions),
    Args = BoundArgs.
he_finish_typed_call_selections(Fun, Args, DisplayArgs, Selections, Out) :-
    member(Selection, Selections),
    he_finish_typed_call(Fun, Args, DisplayArgs, Selection, Out), !.

he_collect_typed_nonerror_solutions(Fun, Args, DisplayArgs, Selections, Solutions) :-
    he_perf_counter_inc(typed_nonerror_solution_collections),
    he_collect_typed_visible_or_all_display_rows(Fun, Args, DisplayArgs, Rows0),
    findall(BoundArgs-Candidate,
            ( member(ok(TypeChain, ReturnType), Selections),
              TypeChain = [->|_],
              member(BoundArgs-BoundDisplay-Raw0, Rows0),
              he_cast_typed_raw_result(Fun, BoundArgs, BoundDisplay, ReturnType, Raw0, Candidate),
              \+ he_error_atom(Candidate)
            ),
            Solutions0),
    length(Solutions0, SolutionCount),
    he_perf_counter_add(typed_nonerror_solution_rows, SolutionCount),
    alpha_list_to_set(Solutions0, Solutions).

he_collect_relaxed_runtime_solutions(Fun, Args, Solutions) :-
    he_perf_counter_inc(relaxed_runtime_solution_collections),
    he_collect_typed_visible_or_all_arg_rows(Fun, Args, Rows0),
    findall(BoundArgs-Candidate,
            ( member(BoundArgs-Candidate, Rows0),
              \+ he_error_atom(Candidate),
              \+ Candidate = [Fun|BoundArgs]
            ),
            Solutions0),
    length(Solutions0, SolutionCount),
    he_perf_counter_add(relaxed_runtime_solution_rows, SolutionCount),
    alpha_list_to_set(Solutions0, Solutions).

he_relaxed_runtime_allowed(Args, _Selections) :-
    he_args_have_runtime_undefined(Args),
    he_args_runtime_relaxation_candidate(Args).

he_args_runtime_relaxation_candidate([Arg|_]) :-
    var(Arg), !.
he_args_runtime_relaxation_candidate([Arg|_]) :-
    is_list(Arg),
    Arg = [Head|_],
    var(Head), !.
he_args_runtime_relaxation_candidate([_|Args]) :-
    he_args_runtime_relaxation_candidate(Args).
he_args_runtime_relaxation_candidate([]) :-
    fail.

he_cast_typed_raw_result(Fun, Args, DisplayArgs, ReturnType, Raw0, Out) :-
    he_maybe_eval_typed_return(ReturnType, Raw0, RawOut),
    ( he_error_atom(RawOut)
    -> Out = RawOut
    ; Fun == 'get-type'
    -> Out = RawOut
    ; RawOut = [Fun|Args]
    -> Out = RawOut
    ; he_cast_result([Fun|DisplayArgs], ReturnType, RawOut, Out)
    ).

he_finish_typed_call(Fun, Args, DisplayArgs, ok(TypeChain, ReturnType), Out) :-
    TypeChain = [->|_],
    he_invoke_typed_visible_or_all(Fun, Args, Raw0),
    he_maybe_eval_typed_return(ReturnType, Raw0, RawOut),
    ( he_error_atom(RawOut)
    -> Out = RawOut
    ; Fun == 'get-type'
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
    -> Out = [Fun|Args]
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
    ( B =:= 0
    -> ( ( float(A)
         ; float(B)
         )
       -> ( A =:= 0
          -> R = 'NaN'
          ;  A > 0
          -> R = inf
          ;  R = '-inf'
          )
       ;  R = ['Error', ['/', A, B], 'DivisionByZero']
       )
    ; integer(A), integer(B)
    -> R is A // B
    ;  R is A / B
    ).
he_fast_typed_call('%', [A, B], _, R) :-
    integer(A), integer(B), !,
    ( B =:= 0
    -> R = ['Error', ['%', A, B], 'DivisionByZero']
    ;  R is A rem B
    ).
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
    he_fast_typed_literal(B),
    ( he_auto_typecheck(true)
    -> 'get-type'(A, TA),
       'get-type'(B, TB),
       ( he_match_types_live(TA, TB)
       -> true
       ;  R = ['Error', ['==', A, B], ['BadArgType', 2, TA, TB]]
       )
    ;  true
    ), !,
    ( var(R) ->
      ( A =@= B -> R = true ; R = false )
    ; true
    ).
he_fast_typed_call('!=', [A, B], _, R) :-
    he_fast_typed_literal(A),
    he_fast_typed_literal(B),
    ( he_auto_typecheck(true)
    -> 'get-type'(A, TA),
       'get-type'(B, TB),
       ( he_match_types_live(TA, TB)
       -> true
       ;  R = ['Error', ['!=', A, B], ['BadArgType', 2, TA, TB]]
       )
    ;  true
    ), !,
    ( var(R) ->
      ( A =@= B -> R = false ; R = true )
    ; true
    ).

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

he_display_state_arg(StateRef, DisplayState) :-
    he_space_ref_atom(StateRef),
    catch(nb_getval(StateRef, Bound), _, fail), !,
    he_display_state_arg(Bound, DisplayState).
he_display_state_arg(State, State) :-
    he_state_handle(State, _), !.

he_display_call_args('change-state!', [State|Rest], [DisplayState|Rest]) :-
    he_display_state_arg(State, DisplayState), !.
he_display_call_args('get-type-space', ['&self'|Rest], ['ModuleSpace(GroundingSpace-top)'|Rest]) :-
    !.
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

he_zero_arg_atom_head_body(Fun, Body) :-
    atom(Fun),
    catch(match('&self', [=, Fun, Body], Body, _), _, fail), !.
he_zero_arg_atom_head_body(Fun, Body) :-
    atom(Fun),
    catch(match('&self', [=, [Fun], Body], Body, _), _, fail).

he_has_zero_arg_atom_head_equation(Fun) :-
    he_zero_arg_atom_head_body(Fun, _).

he_preserve_zero_arg_eval_body([Head|_]) :-
    atom(Head),
    memberchk(Head, [superpose, hyperpose]).

he_eval_zero_arg_equation_body(Body, Body) :-
    he_preserve_zero_arg_eval_body(Body), !.
he_eval_zero_arg_equation_body(Body, Out) :-
    atom(Body),
    he_has_zero_arg_atom_head_equation(Body), !,
    he_eval_or_reduce([Body], Out).
he_eval_zero_arg_equation_body(Body, Body) :-
    atom(Body), !.
he_eval_zero_arg_equation_body(Body, Out) :-
    eval(Body, Out).

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
    he_runtime_direct_predicate_plan(Fun, Arity, runtime_predicate).

he_call_has_equation(Call) :-
    Call = [Fun],
    atom(Fun),
    he_has_zero_arg_atom_head_equation(Fun), !.
he_call_has_equation(Call) :-
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    copy_term(Args, ArgsCopy),
    he_eq_fact(Fun, Arity, HeadArgs, _),
    HeadArgs = ArgsCopy, !.
he_call_has_equation(Call) :-
    copy_term(Call, CallCopy),
    catch(match('&self', [=, CallCopy, Body], Body, _), _, fail), !.

he_call_has_fun_meta([Fun|Args]) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta(HeadArgs, _), Metas),
    copy_term(HeadArgs-Args, HeadCopy-ArgsCopy),
    HeadCopy = ArgsCopy, !.

% Backend cache invalidation for live `&self` mutations and function metadata.

he_invalidate_compiled_goal_resolution(Fun) :-
    atom(Fun), !,
    retractall(he_compiled_goal_resolution(Fun, _, _)),
    retractall(he_compiled_goal_no_resolution(Fun, _)).
he_invalidate_compiled_goal_resolution(_).

he_invalidate_runtime_callable_head_cache(Fun) :-
    atom(Fun), !,
    retractall(he_runtime_callable_head_cache(Fun)),
    retractall(he_runtime_noncallable_head_cache(Fun)).
he_invalidate_runtime_callable_head_cache(_).

he_invalidate_runtime_direct_predicate_plan_cache(Fun) :-
    atom(Fun), !,
    retractall(he_runtime_direct_predicate_plan_cache(Fun, _, _)).
he_invalidate_runtime_direct_predicate_plan_cache(_).

he_invalidate_call_partial_arity_cache(Fun) :-
    atom(Fun), !,
    retractall(he_call_partial_arity_cache(Fun, _, _)).
he_invalidate_call_partial_arity_cache(_).

he_invalidate_partial_apply_dispatch_plan_cache(Fun) :-
    atom(Fun), !,
    retractall(he_partial_apply_dispatch_plan_cache(Fun, _, _)).
he_invalidate_partial_apply_dispatch_plan_cache(_).

he_invalidate_single_equation_arity_cache(Fun) :-
    atom(Fun), !,
    retractall(he_single_equation_arity_cache(Fun, _, _)).
he_invalidate_single_equation_arity_cache(_).

he_invalidate_all_single_result_plan_caches :-
    retractall(he_single_result_callable_param_positions_cache(_, _, _)),
    retractall(he_single_result_call_plan_cache(_, _, _, _)),
    retractall(he_single_result_ground_memo_cache(_, _, _)),
    retractall(he_single_result_recursive_fun_cache(_, _, _)).

he_invalidate_multi_equation_direct_plan_cache(Fun) :-
    atom(Fun), !,
    retractall(he_multi_equation_direct_plan_cache(Fun, _, _)).
he_invalidate_multi_equation_direct_plan_cache(_).

he_invalidate_native_contract_plan_cache(Fun) :-
    atom(Fun), !,
    retractall(he_native_contract_plan_cache(Fun, _, _)).
he_invalidate_native_contract_plan_cache(_).
he_invalidate_unique_queue_search_plan_cache(Fun) :-
    retractall(he_unique_queue_search_plan_cache(Fun, _, _)).
he_invalidate_unique_queue_search_plan_cache(_).

he_invalidate_backend_fun_caches(Fun) :-
    he_invalidate_runtime_callable_head_cache(Fun),
    he_invalidate_runtime_direct_predicate_plan_cache(Fun),
    he_invalidate_call_partial_arity_cache(Fun),
    he_invalidate_partial_apply_dispatch_plan_cache(Fun),
    he_invalidate_single_equation_arity_cache(Fun),
    he_invalidate_all_single_result_plan_caches,
    he_invalidate_multi_equation_direct_plan_cache(Fun),
    he_invalidate_native_contract_plan_cache(Fun),
    he_invalidate_unique_queue_search_plan_cache(Fun),
    he_invalidate_effect_only_safe_fun_cache(Fun).

he_space_fact_added_hook('&self', [=, [Fun|_], _]) :-
    atom(Fun), !,
    he_invalidate_compiled_goal_resolution(Fun),
    he_invalidate_backend_fun_caches(Fun).
he_space_fact_removed_hook('&self', [=, [Fun|_], _]) :-
    atom(Fun), !,
    he_invalidate_compiled_goal_resolution(Fun),
    he_invalidate_backend_fun_caches(Fun).
he_fun_registered_hook(Fun) :-
    atom(Fun), !,
    he_invalidate_backend_fun_caches(Fun).
he_fun_removed_hook(Fun) :-
    atom(Fun), !,
    he_invalidate_compiled_goal_resolution(Fun),
    he_invalidate_backend_fun_caches(Fun).

he_compiled_goal_user_functor(Fun, Arity, UserFun) :-
    he_compiled_goal_resolution(Fun, Arity, UserFun), !.
he_compiled_goal_user_functor(Fun, Arity, _) :-
    he_compiled_goal_no_resolution(Fun, Arity), !,
    fail.
he_compiled_goal_user_functor(Fun, Arity, UserFun) :-
    metta_user_functor(Fun, UserFun),
    he_perf_counter_inc(current_predicate_compiled_goal_resolution_checks),
    current_predicate(UserFun/Arity), !,
    he_perf_counter_inc(current_predicate_compiled_goal_resolution_hits),
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
    he_compiled_equation_goal(Call, Out, Goal), !.
he_compiled_user_goal([Fun|Args], Out, Goal) :-
    he_profile_enabled,
    atom(Fun),
    fun(Fun),
    append(Args, [Out], CallArgs),
    length(CallArgs, Arity),
    he_compiled_goal_user_functor(Fun, Arity, UserFun),
    Goal =.. [UserFun|CallArgs].

% Native/direct call routing for user calls.
% Order matters: native contracts and explicit compiled-equation contracts
% stay ahead of broader compiled/runtime fallback lanes.

he_build_user_call_native_or_direct_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_build_native_contract_goal(Call, Out, Goal), !.
he_build_user_call_native_or_direct_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_compiled_equation_goal(Call, Out, CompiledGoal), !,
    Goal = he_call_compiled_equation_or_self(Call, CompiledGoal, Out).
he_build_user_call_native_or_direct_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_compiled_user_goal(Call, Out, CompiledGoal), !,
    Goal = he_call_compiled_or_self(Call, CompiledGoal, Out).
he_build_user_call_native_or_direct_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun|Args],
    atom(Fun),
    append(Args, [Out], CallArgs),
    length(CallArgs, Arity),
    he_runtime_direct_predicate_plan(Fun, Arity, runtime_predicate),
    Goal =.. [Fun|CallArgs], !.
he_build_user_call_native_or_direct_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_call_has_fun_meta(Call),
    Call = [Fun|Args],
    atom(Fun),
    metta_user_functor(Fun, UserFun),
    append(Args, [Out], CallArgs),
    Goal =.. [UserFun|CallArgs], !.

he_build_user_call_or_eval(Call, Out, Goal) :-
    he_profile_enabled,
    he_build_user_call_native_or_direct_goal(Call, Out, Goal), !.
he_build_user_call_or_eval(Call, Out, he_eval_or_reduce(Call, Out)).

he_build_user_call_direct_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_build_user_call_native_or_direct_goal(Call, Out, Goal), !.

% Stream routing mirrors the direct-call router, but prefers stream-capable
% native/compiled lanes before dropping to general result streaming.

he_build_native_contract_stream_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun, Board, Dir],
    atom(Fun),
    var(Dir),
    he_native_contract_plan(Fun, 2, move9), !,
    Goal = he_native_move9_stream_call(Board, Dir, Out).

he_build_native_queue_search_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun, StartExpr],
    atom(Fun),
    ground(StartExpr),
    he_unique_queue_search_plan(Fun, 1, Plan),
    Plan \== none, !,
    Goal = he_native_unique_queue_search_call(Plan, StartExpr, Out).
he_build_native_queue_search_goal(Call, Out, Goal) :-
    he_profile_enabled,
    Call = [Fun, StartExpr, LimitExpr],
    atom(Fun),
    ground(StartExpr),
    ground(LimitExpr),
    he_unique_queue_search_plan(Fun, 2, Plan),
    Plan \== none, !,
    Goal = he_native_unique_queue_search_limited_call(Plan, StartExpr, LimitExpr, Out).

he_build_user_call_stream_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_build_native_contract_stream_goal(Call, Out, Goal), !.
he_build_user_call_stream_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_build_native_contract_goal(Call, Out, Goal), !.
he_build_user_call_stream_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_compiled_equation_goal(Call, Out, CompiledGoal), !,
    Goal = he_call_compiled_result_stream(Call, CompiledGoal, Out).
he_build_user_call_stream_goal(Call, Out, Goal) :-
    he_profile_enabled,
    he_compiled_user_goal(Call, Out, CompiledGoal), !,
    Goal = he_call_compiled_result_stream(Call, CompiledGoal, Out).

% Generic HE runtime evaluation and dynamic-call fallback.
% Clause order matters: cheap structural exits come first, then native/compiled
% routes, then the broader eval/reduce fallback.

he_call_compiled_result_stream(Call, Goal, Out) :-
    call(Goal),
    he_capture_bound_call_out(Call, Out, BoundCall, BoundOut),
    Call = BoundCall,
    Out = BoundOut.

he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    var(Fun), !,
    Out = [Fun|Args].
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    is_list(Fun),
    \+ he_callable_data_head(Fun), !,
    Out = [Fun|Args].
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    is_list(Fun), !,
    ( he_call_has_equation(Call)
    -> catch(match('&self', [=, Call, Body], Body, _), _, fail),
       eval(Body, Out)
    ;  ( he_eval_or_reduce(Fun, Callable)
       -> ( Callable \=@= Fun,
            he_apply_callable_result(Callable, Args, Applied)
          -> Out = Applied
          ;  Out = [Fun|Args]
          )
       ;  Out = [Fun|Args]
       )
    ).
he_eval_or_reduce(['union-atom', A, B], Out) :-
    he_profile_enabled, !,
    he_union_atom(A, B, Out).
he_eval_or_reduce([Fun], Out) :-
    he_profile_enabled,
    he_zero_arg_atom_head_body(Fun, Body), !,
    he_eval_zero_arg_equation_body(Body, Out).
he_eval_or_reduce([iterate, I, N, State, Step], Out) :-
    he_profile_enabled,
    integer(I),
    integer(N),
    N >= 0, !,
    he_native_iterate(I, N, State, Step, Out).
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    Call = [Fun|Args],
    nonvar(Fun),
    \+ he_runtime_callable_head(Fun),
    \+ he_py_callable_head(Fun), !,
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
    he_build_native_contract_goal(Call, Out, Goal), !,
    call(Goal).
he_eval_or_reduce(Call, Out) :-
    he_profile_enabled,
    he_compiled_equation_goal(Call, Out, Goal), !,
    he_call_compiled_or_self(Call, Goal, Out).
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

he_eval_ambiguous_list_head_expr(HeadExpr, TailExprs, Out) :-
    he_eval_ambiguous_head_expr(HeadExpr, HeadValue),
    ( he_ambiguous_callable_head_value(HeadValue)
    -> he_eval_ambiguous_eval_args(TailExprs, Args),
       he_apply_callable_result(HeadValue, Args, Out)
    ;  he_eval_ambiguous_eval_args(TailExprs, TailValues),
       Out = [HeadValue|TailValues]
    ).

he_eval_ambiguous_head_expr([Head|RawArgs], HeadValue) :-
    atom(Head),
    he_effect_only_safe_call(Head, RawArgs, []), !,
    ( once(he_dynamic_call_raw(Head, RawArgs, HeadValue))
    -> true
    ;  he_eval_ambiguous_eval_args(RawArgs, EvalArgs),
       HeadValue = [Head|EvalArgs]
    ).
he_eval_ambiguous_head_expr([Head|RawArgs], HeadValue) :-
    !,
    State = state(no_success),
    ( he_dynamic_call_raw(Head, RawArgs, HeadValue),
      nb_setarg(1, State, success)
    ; arg(1, State, no_success),
      he_eval_ambiguous_eval_args(RawArgs, EvalArgs),
      HeadValue = [Head|EvalArgs]
    ).
he_eval_ambiguous_head_expr(HeadExpr, HeadValue) :-
    translate_expr(HeadExpr, HeadGoals, HeadValue),
    call_goals(HeadGoals).

he_eval_ambiguous_eval_args([], []).
he_eval_ambiguous_eval_args([Expr|Exprs], [Value|Values]) :-
    translate_expr(Expr, Goals, Value),
    call_goals(Goals),
    he_eval_ambiguous_eval_args(Exprs, Values).

he_ambiguous_callable_head_value(Value) :-
    nonvar(Value),
    ( Value = partial(_, _)
    ; atom(Value), fun(Value)
    ; he_py_callable_head(Value)
    ).

% Dynamic runtime-call routing before the generic evaluator.
% These paths separate raw special forms, partial application, plainly
% noncallable heads, and the remaining eval/reduce fallback.

he_dynamic_call_raw(Head, RawArgs, Out) :-
    var(Head), !,
    he_eval_runtime_args(RawArgs, EvalArgs),
    ( var(Head)
    -> Out = [Head|EvalArgs]
    ;  he_eval_or_reduce([Head|EvalArgs], Out)
    ).
he_dynamic_call_raw(Head, RawArgs, Out) :-
    nonvar(Head),
    Head == quote, !,
    he_runtime_special_call(quote, RawArgs, Out).
he_dynamic_call_raw(Head, RawArgs, Out) :-
    nonvar(Head),
    Head == capture, !,
    he_runtime_special_call(capture, RawArgs, Out).
he_dynamic_call_raw(Head, RawArgs, Out) :-
    nonvar(Head),
    Head = partial(Fun, Bound),
    atom(Fun),
    he_eval_runtime_args(RawArgs, EvalArgs),
    append(Bound, EvalArgs, AllArgs),
    he_build_partial_apply_direct_goal(Fun, AllArgs, Out, Goal), !,
    call(Goal).
he_dynamic_call_raw(Head, RawArgs, Out) :-
    number(Head), !,
    once(he_eval_runtime_args(RawArgs, EvalArgs)),
    Out = [Head|EvalArgs].
he_dynamic_call_raw(Head, RawArgs, Out) :-
    atomic(Head),
    \+ he_py_callable_head(Head),
    \+ atom(Head), !,
    he_perf_counter_inc(runtime_noncallable_head_scalar_fast_paths),
    once(he_eval_runtime_args(RawArgs, EvalArgs)),
    Out = [Head|EvalArgs].
he_dynamic_call_raw(Head, RawArgs, Out) :-
    is_list(Head),
    \+ he_callable_data_head(Head), !,
    he_perf_counter_inc(runtime_noncallable_head_list_data_fast_paths),
    once(he_eval_runtime_args(RawArgs, EvalArgs)),
    Out = [Head|EvalArgs].
he_dynamic_call_raw(Head, RawArgs, Out) :-
    atom(Head),
    \+ he_space_ref_atom(Head),
    he_runtime_noncallable_head_cache(Head), !,
    he_perf_counter_inc(runtime_noncallable_head_negative_cache_fast_paths),
    once(he_eval_runtime_args(RawArgs, EvalArgs)),
    Out = [Head|EvalArgs].
he_dynamic_call_raw(Head, RawArgs, Out) :-
    ( he_noncallable_runtime_head(Head)
    -> once(he_eval_runtime_args(RawArgs, EvalArgs)),
       Out = [Head|EvalArgs]
    ;  he_eval_runtime_args(RawArgs, EvalArgs),
       he_eval_or_reduce([Head|EvalArgs], Out)
    ).

he_dynamic_var_head_call_raw(Head, RawArgs, Out) :-
    var(Head), !,
    he_eval_runtime_args(RawArgs, EvalArgs),
    ( var(Head)
    -> Out = [Head|EvalArgs]
    ;  he_dynamic_var_head_call_eval(Head, EvalArgs, Out)
    ).
he_dynamic_var_head_call_raw(Head, RawArgs, Out) :-
    he_eval_runtime_args(RawArgs, EvalArgs),
    he_dynamic_var_head_call_eval(Head, EvalArgs, Out).

% Var-head calls get one more chance to become direct once their head and args
% have already been evaluated.

he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    nonvar(Head),
    Head = partial(Fun, Bound),
    atom(Fun),
    append(Bound, EvalArgs, AllArgs),
    he_build_partial_apply_direct_goal(Fun, AllArgs, Out, Goal), !,
    he_perf_counter_inc(var_head_partial_direct_hits),
    call(Goal).
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    number(Head), !,
    Out = [Head|EvalArgs].
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    atomic(Head),
    \+ he_py_callable_head(Head),
    \+ atom(Head), !,
    he_perf_counter_inc(runtime_noncallable_head_scalar_fast_paths),
    Out = [Head|EvalArgs].
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    is_list(Head),
    \+ he_callable_data_head(Head), !,
    Out = [Head|EvalArgs].
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    atom(Head),
    \+ he_space_ref_atom(Head),
    he_runtime_noncallable_head_cache(Head), !,
    he_perf_counter_inc(runtime_noncallable_head_negative_cache_fast_paths),
    Out = [Head|EvalArgs].
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    atom(Head),
    \+ he_space_ref_atom(Head),
    he_build_user_call_direct_goal([Head|EvalArgs], Out, Goal), !,
    he_perf_counter_inc(var_head_atom_direct_hits),
    call(Goal).
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    he_noncallable_runtime_head(Head), !,
    Out = [Head|EvalArgs].
he_dynamic_var_head_call_eval(Head, EvalArgs, Out) :-
    he_perf_counter_inc(var_head_direct_fallbacks),
    he_eval_or_reduce([Head|EvalArgs], Out).

% Raw arity-checked special forms that intentionally bypass generic call
% discovery.

he_runtime_special_call(Head, RawArgs, Out) :-
    length(RawArgs, Arity),
    he_surface(Head, ExpectedArity, _Kind, _Scope),
    Arity =\= ExpectedArity, !,
    Out = ['Error', [Head|RawArgs], 'IncorrectNumberOfArguments'].
he_runtime_special_call(quote, [Expr], [quote, Expr]) :- !.
he_runtime_special_call(capture, [Expr], Out) :-
    capture(Expr, Out).

% Runtime-argument evaluation tries hard to preserve already-plain data instead
% of bouncing it back through the generic evaluator.

he_eval_runtime_args([], []).
he_eval_runtime_args([RawArg|RawArgs], [EvalArg|EvalArgs]) :-
    he_eval_runtime_arg(RawArg, EvalArg),
    he_eval_runtime_args(RawArgs, EvalArgs).

he_runtime_raw_data_term(Term) :-
    var(Term), !.
he_runtime_raw_data_term(Term) :-
    atomic(Term), !.
he_runtime_raw_data_term([]) :- !.
he_runtime_raw_data_term([Head|Tail]) :-
    nonvar(Head),
    he_runtime_raw_data_head(Head),
    he_runtime_raw_data_tail(Tail).

he_runtime_raw_data_head(Head) :-
    atom(Head),
    \+ he_space_ref_atom(Head),
    he_runtime_noncallable_head_cache(Head), !.
he_runtime_raw_data_head(Head) :-
    atomic(Head),
    \+ atom(Head), !.
he_runtime_raw_data_head(Head) :-
    is_list(Head),
    \+ he_callable_data_head(Head),
    he_runtime_raw_data_term(Head), !.
he_runtime_raw_data_head(Head) :-
    atom(Head),
    \+ fun(Head),
    \+ he_head_may_denote_callable(Head).

he_runtime_raw_data_tail([]).
he_runtime_raw_data_tail([Elem|Rest]) :-
    he_runtime_raw_data_term(Elem),
    he_runtime_raw_data_tail(Rest).

he_runtime_arg_prefers_raw(Arg) :-
    nonvar(Arg),
    is_list(Arg),
    he_runtime_raw_data_term(Arg).

he_fast_runtime_arg_expr([+, A, B], Out) :-
    number(A),
    number(B), !,
    Out is A + B.
he_fast_runtime_arg_expr([-, A, B], Out) :-
    number(A),
    number(B), !,
    Out is A - B.
he_fast_runtime_arg_expr([*, A, B], Out) :-
    number(A),
    number(B), !,
    Out is A * B.
he_fast_runtime_arg_expr([+, A, [*, B, C]], Out) :-
    number(A),
    number(B),
    number(C), !,
    Out is A + (B * C).
he_fast_runtime_arg_expr([+, [*, A, B], C], Out) :-
    number(A),
    number(B),
    number(C), !,
    Out is (A * B) + C.
he_fast_runtime_arg_expr([Fun, A, B], Out) :-
    nonvar(Fun),
    he_fast_runtime_arg_fun(Fun),
    he_fast_runtime_arg_value(A, AV),
    he_fast_runtime_arg_value(B, BV),
    he_fast_typed_call(Fun, [AV, BV], [], Out).

he_fast_runtime_arg_fun('+').
he_fast_runtime_arg_fun('-').
he_fast_runtime_arg_fun('*').
he_fast_runtime_arg_fun('/').
he_fast_runtime_arg_fun('%').

he_fast_runtime_arg_value(Arg, Eval) :-
    nonvar(Arg),
    is_list(Arg),
    he_fast_runtime_arg_expr(Arg, Eval), !.
he_fast_runtime_arg_value(Arg, Arg) :-
    \+ is_list(Arg).

he_eval_runtime_arg(Arg, Eval) :-
    he_fast_runtime_arg_expr(Arg, Eval), !.
he_eval_runtime_arg(Arg, Arg) :-
    he_runtime_arg_prefers_raw(Arg), !,
    he_perf_counter_inc(runtime_arg_raw_data_fast_paths).
he_eval_runtime_arg(Arg, Eval) :-
    is_list(Arg), !,
    ( catch(eval(Arg, Eval), _, fail)
    ; \+ he_runtime_arg_has_eval_solution(Arg),
      Eval = Arg
    ).
he_eval_runtime_arg(Arg, Arg).

% Runtime head classification keeps the noncallable fast paths honest while the
% callable cache absorbs repeated dynamic dispatch.

he_noncallable_runtime_head(Head) :-
    he_perf_counter_inc(runtime_noncallable_head_checks),
    he_noncallable_runtime_head_1(Head).

he_noncallable_runtime_head_1(Head) :-
    nonvar(Head),
    \+ ( compound(Head),
         Head = partial(_, _)
       ),
    \+ he_py_callable_head(Head),
    \+ he_runtime_callable_head(Head),
    \+ ( is_list(Head),
         he_callable_data_head(Head)
       ),
    ( is_list(Head)
    -> he_perf_counter_inc(runtime_noncallable_head_list_data_hits)
    ;  true
    ).

he_runtime_arg_has_eval_solution(Arg) :-
    copy_term(Arg, Probe),
    catch(once(eval(Probe, _)), _, fail).

he_apply_callable_result(partial(Fun, Bound), Args, Out) :-
    append(Bound, Args, AllArgs),
    ( he_build_partial_apply_direct_goal(Fun, AllArgs, Out, Goal)
    -> call(Goal)
    ;  he_perf_counter_inc(partial_apply_direct_fallbacks),
       he_eval_or_reduce([Fun|AllArgs], Out)
    ).
he_apply_callable_result(Fun, Args, Out) :-
    he_py_callable_head(Fun), !,
    py_call_callable(Fun, Args, Out).
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

he_union_atom(A, B, Out) :-
    nonvar(Out),
    is_list(B), !,
    once(append(A, B, Out)).
he_union_atom(A, B, Out) :-
    nonvar(Out),
    is_list(A), !,
    once(append(A, B, Out)).
he_union_atom(A, B, Out) :-
    append(A, B, Out).

he_runtime_callable_head(Fun) :-
    he_perf_counter_inc(runtime_callable_head_checks),
    he_runtime_callable_head_1(Fun).

he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    he_runtime_callable_head_cache(Fun), !,
    he_perf_counter_inc(runtime_callable_head_cache_hits).
he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    \+ he_space_ref_atom(Fun),
    he_runtime_noncallable_head_cache(Fun), !,
    he_perf_counter_inc(runtime_callable_head_negative_cache_hits),
    fail.
he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    he_has_zero_arg_atom_head_equation(Fun), !,
    he_perf_counter_inc(runtime_callable_head_zero_arg_equation_hits),
    assertz(he_runtime_callable_head_cache(Fun)).
he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    \+ he_he_data_shadowed_fun(Fun),
    he_runtime_predicate_head(Fun), !,
    he_perf_counter_inc(runtime_callable_head_predicate_hits),
    assertz(he_runtime_callable_head_cache(Fun)).
he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    is_list(Metas), Metas \= [], !,
    he_perf_counter_inc(runtime_callable_head_meta_hits),
    assertz(he_runtime_callable_head_cache(Fun)).
he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    he_space_ref_atom(Fun),
    py_resolve_value(Fun, Callable),
    py_callable(Callable), !,
    he_perf_counter_inc(runtime_callable_head_py_hits).
he_runtime_callable_head_1(Fun) :-
    atom(Fun),
    \+ he_space_ref_atom(Fun),
    he_perf_counter_inc(runtime_callable_head_negative_cache_stores),
    assertz(he_runtime_noncallable_head_cache(Fun)),
    fail.
he_runtime_callable_head_1(Fun) :-
    compound(Fun),
    Fun = partial(_, _), !,
    he_perf_counter_inc(runtime_callable_head_partial_hits).

he_runtime_predicate_head(Fun) :-
    he_runtime_direct_predicate_plan(Fun, _Arity, runtime_predicate).

he_call_or_self(Fun, Args, Out) :-
    Fun == foldl,
    Args = [Func, List, Init],
    is_list(List), !,
    he_foldl_reduce(List, Func, Init, Out).
he_call_or_self(Fun, Args, Out) :-
    Fun == maplist,
    Args = [Func, List],
    is_list(List), !,
    he_maplist_reduce(List, Func, Out).
he_call_or_self(Fun, Args, Out) :-
    Fun == 'map-atom',
    Args = [List, Func],
    is_list(List), !,
    he_maplist_reduce(List, Func, Out).
he_call_or_self(Fun, Args, Out) :-
    Fun == 'union-atom',
    Args = [A, B], !,
    he_union_atom(A, B, Out).
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
    ( he_call_has_exact_out_arity(Fun, SuppliedOutArity)
    -> Decision = none
    ; he_call_known_full_out_arity(Fun, SuppliedOutArity, FullOutArity),
      FullOutArity > SuppliedOutArity
    -> Decision = partial
    ;  Decision = none
    ),
    assertz(he_call_partial_arity_cache(Fun, Supplied, Decision)).

he_call_has_exact_out_arity(Fun, ExpectedOutArity) :-
    he_builtin_type(Fun, TypeChain),
    TypeChain = [->|TypeItems],
    length(TypeItems, ExpectedOutArity), !.
he_call_has_exact_out_arity(Fun, ExpectedOutArity) :-
    catch(arity(Fun, ExpectedOutArity), _, fail), !.
he_call_has_exact_out_arity(Fun, ExpectedOutArity) :-
    he_profile_enabled,
    he_eq_fact(Fun, HeadArity, _, _),
    ActualOutArity is HeadArity + 1,
    ActualOutArity =:= ExpectedOutArity, !.
he_call_has_exact_out_arity(Fun, ExpectedOutArity) :-
    he_runtime_direct_predicate_plan(Fun, ExpectedOutArity, runtime_predicate).

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
    he_runtime_direct_predicate_plan(Fun, FullOutArity, runtime_predicate).

he_partial_apply_dispatch_plan(Fun, OutArity, Plan) :-
    he_partial_apply_dispatch_plan_cache(Fun, OutArity, Plan), !,
    he_perf_counter_inc(partial_apply_dispatch_plan_cache_hits).
he_partial_apply_dispatch_plan(Fun, OutArity, Plan) :-
    ( he_partial_apply_dispatch_plan_1(Fun, OutArity, Plan0)
    -> Plan = Plan0
    ;  Plan = none
    ),
    he_perf_counter_inc(partial_apply_dispatch_plan_cache_stores),
    assertz(he_partial_apply_dispatch_plan_cache(Fun, OutArity, Plan)).

he_partial_apply_dispatch_plan_1(Fun, OutArity, compiled_user) :-
    atom(Fun),
    he_compiled_goal_user_functor(Fun, OutArity, _), !.
he_partial_apply_dispatch_plan_1(Fun, OutArity, runtime_predicate) :-
    atom(Fun),
    he_runtime_direct_predicate_plan(Fun, OutArity, runtime_predicate), !.
he_partial_apply_dispatch_plan_1(Fun, _OutArity, zero_arg_equation) :-
    atom(Fun),
    he_has_zero_arg_atom_head_equation(Fun), !.

he_build_partial_apply_direct_goal(Fun, AllArgs, Out, Goal) :-
    atom(Fun),
    length(AllArgs, Supplied),
    OutArity is Supplied + 1,
    he_partial_apply_dispatch_plan(Fun, OutArity, Plan),
    Plan \== none,
    Call = [Fun|AllArgs],
    he_partial_apply_plan_goal(Plan, Call, Out, Goal).

he_partial_apply_plan_goal(compiled_user, Call, Out, Goal) :-
    he_perf_counter_inc(partial_apply_direct_compiled_user_hits),
    he_build_user_call_direct_goal(Call, Out, Goal).
he_partial_apply_plan_goal(runtime_predicate, [Fun|Args], Out, Goal) :-
    he_perf_counter_inc(partial_apply_direct_runtime_predicate_hits),
    append(Args, [Out], CallArgs),
    Goal =.. [Fun|CallArgs].
he_partial_apply_plan_goal(zero_arg_equation, [Fun], Out, Goal) :-
    he_perf_counter_inc(partial_apply_direct_zero_arg_equation_hits),
    Goal = he_eval_or_reduce([Fun], Out).

he_partial_arity_probe_limit(32).

he_single_equation_call([Fun|Args]) :-
    atom(Fun),
    length(Args, Arity),
    he_single_equation_arity(Fun, Arity).

he_single_equation_arity(Fun, Arity) :-
    he_single_equation_arity_cache(Fun, Arity, single), !.
he_single_equation_arity(Fun, Arity) :-
    he_single_equation_arity_cache(Fun, Arity, multiple), !,
    fail.
he_single_equation_arity(Fun, Arity) :-
    findall(1, he_eq_fact(Fun, Arity, _, _), Matches),
    ( Matches = [_]
    -> Decision = single
    ;  Decision = multiple
    ),
    assertz(he_single_equation_arity_cache(Fun, Arity, Decision)),
    Decision == single.

he_nth1_eq(1, [Head|_], Value) :-
    Head == Value, !.
he_nth1_eq(N, List, Value) :-
    var(N), !,
    he_nth1_eq_from(List, Value, 1, N).
he_nth1_eq(N, [_|Tail], Value) :-
    N > 1,
    N1 is N - 1,
    he_nth1_eq(N1, Tail, Value).

he_nth1_eq_from([Head|_], Value, N, N) :-
    Head == Value.
he_nth1_eq_from([_|Tail], Value, N0, N) :-
    N1 is N0 + 1,
    he_nth1_eq_from(Tail, Value, N1, N).

he_single_result_callable_param_positions(Fun, Arity, Positions) :-
    he_single_result_callable_param_positions_cache(Fun, Arity, Positions), !.
he_single_result_callable_param_positions(Fun, Arity, Positions) :-
    ( he_single_equation_arity(Fun, Arity),
      once(he_eq_fact(Fun, Arity, HeadArgs, Body))
    -> findall(Pos,
               he_single_result_callable_param_position_in_expr(Body, HeadArgs, Pos),
               Positions0),
       sort(Positions0, Positions)
    ;  Positions = []
    ),
    assertz(he_single_result_callable_param_positions_cache(Fun, Arity, Positions)).

he_single_result_callable_param_position_in_expr(Expr, HeadArgs, Pos) :-
    nonvar(Expr),
    Expr = [Head|_],
    var(Head),
    he_nth1_eq(Pos, HeadArgs, Head).
he_single_result_callable_param_position_in_expr(Expr, HeadArgs, Pos) :-
    nonvar(Expr),
    is_list(Expr),
    Expr = [Head|Args],
    member(Item, [Head|Args]),
    he_single_result_callable_param_position_in_expr(Item, HeadArgs, Pos).
he_single_result_callable_param_position_in_expr(Expr, HeadArgs, Pos) :-
    nonvar(Expr),
    compound(Expr),
    \+ is_list(Expr),
    compound_name_arguments(Expr, _Name, Args),
    member(Arg, Args),
    he_single_result_callable_param_position_in_expr(Arg, HeadArgs, Pos).

he_single_result_callable_key(_Args, [], []) :- !.
he_single_result_callable_key(Args, Positions, Key) :-
    findall(Arg,
            ( member(Pos, Positions),
              nth1(Pos, Args, Arg)
            ),
            Key).

he_bind_single_result_callable_args([], _HeadArgs, _Args).
he_bind_single_result_callable_args([Pos|Positions], HeadArgs, Args) :-
    nth1(Pos, HeadArgs, HeadArg),
    nth1(Pos, Args, Arg),
    HeadArg = Arg,
    he_bind_single_result_callable_args(Positions, HeadArgs, Args).

he_single_result_runtime_builtin_head(Head) :-
    he_effect_only_pure_builtin_head(Head).
he_single_result_runtime_builtin_head(is-expr).
he_single_result_runtime_builtin_head(cons).
he_single_result_runtime_builtin_head('cons-atom').
he_single_result_runtime_builtin_head('decons-atom').
he_single_result_runtime_builtin_head('size-atom').
he_single_result_runtime_builtin_head('car-atom').

he_single_result_safe_expr(Expr) :-
    he_single_result_safe_expr(Expr, []).

he_single_result_safe_expr(Expr, _) :-
    var(Expr), !.
he_single_result_safe_expr(Expr, _) :-
    atomic(Expr), !.
he_single_result_safe_expr([if, Cond, Then, Else], Stack) :-
    !,
    he_single_result_safe_expr(Cond, Stack),
    he_single_result_safe_expr(Then, Stack),
    he_single_result_safe_expr(Else, Stack).
he_single_result_safe_expr([if, Cond, Then], Stack) :-
    !,
    he_single_result_safe_expr(Cond, Stack),
    he_single_result_safe_expr(Then, Stack).
he_single_result_safe_expr([let, _Pat, Val, In], Stack) :-
    !,
    he_single_result_safe_expr(Val, Stack),
    he_single_result_safe_expr(In, Stack).
he_single_result_safe_expr([chain, Val, _Pat, In], Stack) :-
    !,
    he_single_result_safe_expr(Val, Stack),
    he_single_result_safe_expr(In, Stack).
he_single_result_safe_expr(['let*', Binds, Body], Stack) :-
    !,
    letstar_to_rec_let(Binds, Body, RecLet),
    he_single_result_safe_expr(RecLet, Stack).
he_single_result_safe_expr([Head|Args], Stack) :-
    !,
    he_single_result_safe_call_expr([Head|Args], Stack).
he_single_result_safe_expr(Expr, Stack) :-
    compound_name_arguments(Expr, _Name, Args),
    maplist({Stack}/[Arg]>>he_single_result_safe_expr(Arg, Stack), Args).

he_single_result_safe_call_expr([Head|_Args], _Stack) :-
    var(Head), !,
    fail.
he_single_result_safe_call_expr([Head|Args], Stack) :-
    is_list(Head),
    \+ he_callable_data_head(Head), !,
    maplist({Stack}/[Item]>>he_single_result_safe_expr(Item, Stack),
            [Head|Args]).
he_single_result_safe_call_expr([partial(Fun, Bound)|Args], Stack) :-
    atom(Fun), !,
    append(Bound, Args, AllArgs),
    he_single_result_safe_call_expr([Fun|AllArgs], Stack).
he_single_result_safe_call_expr([Head|Args], Stack) :-
    atom(Head),
    he_single_result_safe_builtin_call(Head, Args, Stack), !.
he_single_result_safe_call_expr([Head|Args], Stack) :-
    atom(Head),
    length(Args, Arity),
    memberchk(Head/Arity, Stack), !,
    maplist({Stack}/[Arg]>>he_single_result_safe_expr(Arg, Stack), Args).
he_single_result_safe_call_expr([Head|Args], Stack) :-
    atom(Head),
    maplist({Stack}/[Arg]>>he_single_result_safe_expr(Arg, Stack), Args),
    he_single_result_call_plan(Head, Args, Stack, safe).

he_single_result_safe_builtin_call(eval, [Arg], Stack) :-
    he_single_result_safe_expr(Arg, Stack).
he_single_result_safe_builtin_call(reduce, [Arg], Stack) :-
    he_single_result_safe_expr(Arg, Stack).
he_single_result_safe_builtin_call(quote, [_Arg], _Stack).
he_single_result_safe_builtin_call(Head, Args, Stack) :-
    he_single_result_runtime_builtin_head(Head),
    maplist({Stack}/[Arg]>>he_single_result_safe_expr(Arg, Stack), Args).

he_single_result_call_plan(Fun, Args, Decision) :-
    he_single_result_call_plan(Fun, Args, [], Decision).

he_single_result_call_plan(Fun, Args, Stack, Decision) :-
    atom(Fun),
    length(Args, Arity),
    ( memberchk(Fun/Arity, Stack)
    -> Decision = safe
    ; he_single_result_callable_param_positions(Fun, Arity, Positions),
      he_single_result_callable_key(Args, Positions, Key),
      ( he_single_result_call_plan_cache(Fun, Arity, Key, CachedDecision)
      -> Decision = CachedDecision
      ;  he_single_result_call_plan_1(Fun, Arity, Positions, Args,
                                      [Fun/Arity|Stack], Decision0),
         assertz(he_single_result_call_plan_cache(Fun, Arity, Key, Decision0)),
         Decision = Decision0
      )
    ).

he_single_result_call_plan_1(Fun, Arity, Positions, Args, Stack, safe) :-
    he_single_equation_arity(Fun, Arity),
    once(he_eq_fact(Fun, Arity, HeadArgs0, Body0)),
    copy_term(HeadArgs0-Body0, HeadArgs-Body),
    he_bind_single_result_callable_args(Positions, HeadArgs, Args),
    he_single_result_safe_expr(Body, Stack), !.
he_single_result_call_plan_1(_Fun, _Arity, _Positions, _Args, _Stack, unsafe).

he_single_result_ground_memo_candidate(Fun, Args) :-
    ground(Args),
    length(Args, Arity),
    he_single_result_recursive_fun(Fun, Arity).

he_single_result_recursive_fun(Fun, Arity) :-
    he_single_result_recursive_fun_cache(Fun, Arity, yes), !.
he_single_result_recursive_fun(Fun, Arity) :-
    he_single_result_recursive_fun_cache(Fun, Arity, no), !,
    fail.
he_single_result_recursive_fun(Fun, Arity) :-
    ( once(( he_eq_fact(Fun, Arity, _HeadArgs, Body),
             he_expr_calls_fun_at_least(Fun, Body, 2)
           ))
    -> Decision = yes
    ;  Decision = no
    ),
    assertz(he_single_result_recursive_fun_cache(Fun, Arity, Decision)),
    Decision == yes.

he_expr_calls_fun(Fun, Expr) :-
    he_expr_call_count(Fun, Expr, Count),
    Count > 0.

he_expr_calls_fun_at_least(Fun, Expr, Need) :-
    he_expr_call_count(Fun, Expr, Count),
    Count >= Need.

he_expr_call_count(Fun, Expr, Count) :-
    he_expr_call_count(Fun, Expr, 0, Count).

he_expr_call_count(_Fun, Expr, Count, Count) :-
    var(Expr), !.
he_expr_call_count(_Fun, Expr, Count, Count) :-
    atomic(Expr), !.
he_expr_call_count(_Fun, Expr, Count, Count) :-
    nonvar(Expr),
    Expr = [quote, _Quoted], !,
    true.
he_expr_call_count(Fun, Expr, Count0, Count) :-
    nonvar(Expr),
    is_list(Expr),
    Expr = [Head|Items],
    ( Head == Fun
    -> Count1 is Count0 + 1
    ;  he_expr_call_count(Fun, Head, Count0, Count1)
    ),
    he_expr_call_count_list(Fun, Items, Count1, Count).
he_expr_call_count(Fun, Expr, Count0, Count) :-
    nonvar(Expr),
    compound(Expr),
    \+ is_list(Expr),
    compound_name_arguments(Expr, _Name, Args),
    he_expr_call_count_list(Fun, Args, Count0, Count).

he_expr_call_count_list(_Fun, [], Count, Count).
he_expr_call_count_list(Fun, [Item|Items], Count0, Count) :-
    he_expr_call_count(Fun, Item, Count0, Count1),
    he_expr_call_count_list(Fun, Items, Count1, Count).

he_single_result_compiled_call_or_self(Call, _Goal, Out) :-
    Call = [Fun|Args],
    atom(Fun),
    he_single_result_ground_memo_candidate(Fun, Args),
    he_single_result_call_plan(Fun, Args, safe),
    he_single_result_ground_memo_hit(Fun, Args, Out), !.
he_single_result_compiled_call_or_self(Call, Goal, Out) :-
    Call = [Fun|Args],
    atom(Fun),
    he_single_result_call_plan(Fun, Args, safe),
    he_note_single_result_direct_attempt,
    once(( call(Goal),
           he_capture_bound_call_out(Call, Out, BoundCall, BoundOut)
         )),
    he_note_single_result_direct_hit(BoundOut),
    Call = BoundCall,
    Out = BoundOut,
    he_single_result_ground_memo_store(Fun, Args, BoundOut).

he_single_result_ground_memo_hit(Fun, Args, Out) :-
    he_single_result_ground_memo_candidate(Fun, Args),
    he_single_result_ground_memo_cache(Fun, Args, Out0), !,
    Out = Out0.

he_single_result_ground_memo_store(Fun, Args, Out) :-
    he_single_result_ground_memo_candidate(Fun, Args),
    ground(Out),
    \+ he_empty_result(Out),
    \+ he_error_atom(Out), !,
    ( he_single_result_ground_memo_cache(Fun, Args, _)
    -> true
    ;  assertz(he_single_result_ground_memo_cache(Fun, Args, Out))
    ).
he_single_result_ground_memo_store(_, _, _).

he_note_single_result_direct_attempt :-
    he_perf_counters_enabled, !,
    he_perf_counter_inc(compiled_equation_goal_single_result_calls).
he_note_single_result_direct_attempt.

he_note_single_result_direct_hit(BoundOut) :-
    he_perf_counters_enabled, !,
    he_perf_counter_inc(compiled_equation_goal_single_direct_hits),
    he_perf_counter_add(compiled_equation_goal_raw_rows, 1),
    ( he_visible_result(BoundOut)
    -> he_perf_counter_add(compiled_equation_goal_visible_rows, 1)
    ;  true
    ).
he_note_single_result_direct_hit(_).

he_invalidate_effect_only_safe_fun_cache(Fun) :-
    atom(Fun), !,
    retractall(he_effect_only_safe_fun_cache(Fun, _, _)),
    retractall(he_effect_only_native_plan_cache(Fun, _, _)).
he_invalidate_effect_only_safe_fun_cache(_).

he_memberchk_eq(V, [H|_]) :-
    V == H, !.
he_memberchk_eq(V, [_|T]) :-
    he_memberchk_eq(V, T).

he_var_unused_in_expr(Var, Expr) :-
    var(Var),
    term_variables(Expr, Vars),
    \+ he_memberchk_eq(Var, Vars).

he_effect_only_pure_builtin_head('+').
he_effect_only_pure_builtin_head('-').
he_effect_only_pure_builtin_head('*').
he_effect_only_pure_builtin_head('/').
he_effect_only_pure_builtin_head('%').
he_effect_only_pure_builtin_head('<').
he_effect_only_pure_builtin_head('>').
he_effect_only_pure_builtin_head('<=').
he_effect_only_pure_builtin_head('>=').
he_effect_only_pure_builtin_head('==').
he_effect_only_pure_builtin_head('!=').

he_effect_only_data_head(Head) :-
    atom(Head),
    \+ he_space_ref_atom(Head),
    \+ he_has_zero_arg_atom_head_equation(Head),
    \+ he_runtime_predicate_head(Head),
    \+ catch(nb_getval(Head, _), _, fail),
    \+ he_py_callable_head(Head).

he_effect_only_safe_query_expr(Expr, Stack) :-
    nonvar(Expr),
    Expr = [Head, Space, Pattern, Body],
    Head == match,
    !,
    he_effect_only_safe_arg_expr(Space, Stack),
    he_effect_only_safe_arg_expr(Pattern, Stack),
    he_effect_only_safe_arg_expr(Body, Stack).
he_effect_only_safe_query_expr(Expr, Stack) :-
    nonvar(Expr),
    Expr = [Head, Inner],
    Head == once,
    !,
    he_effect_only_safe_query_expr(Inner, Stack).
he_effect_only_safe_query_expr(Expr, Stack) :-
    nonvar(Expr),
    Expr = [Head, Inner],
    Head == collapse,
    !,
    he_effect_only_safe_query_expr(Inner, Stack).
he_effect_only_safe_query_expr(Expr, Stack) :-
    nonvar(Expr),
    Expr = [Head, Inner],
    Head == superpose,
    !,
    he_effect_only_safe_arg_expr(Inner, Stack).

he_effect_only_safe_arg_expr(Expr, Stack) :-
    he_effect_only_safe_query_expr(Expr, Stack), !.
he_effect_only_safe_arg_expr(Expr, Stack) :-
    he_effect_only_safe_expr(Expr, Stack), !.
he_effect_only_safe_arg_expr(Expr, _Stack) :-
    var(Expr), !.
he_effect_only_safe_arg_expr(Expr, _Stack) :-
    atomic(Expr), !.
he_effect_only_safe_arg_expr([Head|Args], Stack) :-
    atom(Head),
    ( he_effect_only_pure_builtin_head(Head)
    ; he_effect_only_data_head(Head)
    ),
    maplist({Stack}/[Arg]>>he_effect_only_safe_arg_expr(Arg, Stack), Args).

he_effect_only_safe_root_expr([Head|Args]) :-
    atom(Head),
    length(Args, Arity),
    maplist({}/[Arg]>>he_effect_only_safe_arg_expr(Arg, []), Args),
    he_effect_only_safe_fun(Head, Arity).

he_effect_only_safe_fun(Fun, Arity) :-
    he_effect_only_safe_fun_cache(Fun, Arity, safe), !.
he_effect_only_safe_fun(Fun, Arity) :-
    he_effect_only_safe_fun_cache(Fun, Arity, unsafe), !,
    fail.
he_effect_only_safe_fun(Fun, Arity) :-
    he_effect_only_safe_fun_1(Fun, Arity, []), !,
    assertz(he_effect_only_safe_fun_cache(Fun, Arity, safe)).
he_effect_only_safe_fun(Fun, Arity) :-
    assertz(he_effect_only_safe_fun_cache(Fun, Arity, unsafe)),
    fail.

he_effect_only_native_plan(Fun, Arity, Plan) :-
    he_effect_only_native_plan_cache(Fun, Arity, Plan), !.
he_effect_only_native_plan(Fun, Arity, Plan) :-
    ( he_effect_only_native_plan_1(Fun, Arity, Plan0)
    -> Plan = Plan0
    ;  Plan = none
    ),
    assertz(he_effect_only_native_plan_cache(Fun, Arity, Plan)).

he_effect_only_native_plan_1(Fun, 2, self_add_branching(Rel, AddOps, RecurOps)) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta([TermArg, DepthArg], Body), Metas),
    Body = [if,
            [==, CondDepth, 0],
            done,
            ['let*', Binds, RecCalls]],
    DepthArg == CondDepth,
    he_effect_only_native_self_add_binds(Binds, TermArg, Rel, AddOps),
    he_effect_only_native_self_add_rec_calls(RecCalls, Fun, TermArg, DepthArg, RecurOps),
    AddOps \= [],
    RecurOps \= [].

he_effect_only_native_self_add_binds(Binds, TermArg, Rel, Ops) :-
    maplist(he_effect_only_native_self_add_bind(TermArg, Rel), Binds, Ops).

he_effect_only_native_self_add_bind(TermArg, Rel, [_Ignore, ['add-atom', '&self', [Rel, [Op, TermArg]]]], Op) :-
    atom(Rel),
    atom(Op).

he_effect_only_native_self_add_rec_calls(RecCalls, Fun, TermArg, DepthArg, Ops) :-
    maplist(he_effect_only_native_self_add_rec_call(Fun, TermArg, DepthArg), RecCalls, Ops).

he_effect_only_native_self_add_rec_call(Fun, TermArg, DepthArg, [Fun, [Op, TermArg], [-, DepthArg, 1]], Op) :-
    atom(Op).

he_effect_only_safe_fun_1(Fun, Arity, Stack) :-
    atom(Fun),
    memberchk(Fun/Arity, Stack), !.
he_effect_only_safe_fun_1(Fun, Arity, Stack) :-
    atom(Fun),
    he_single_equation_arity(Fun, Arity),
    once(he_eq_fact(Fun, Arity, _, Body)),
    he_effect_only_safe_expr(Body, [Fun/Arity|Stack]).

he_effect_only_safe_expr(Expr) :-
    he_effect_only_safe_expr(Expr, []).

he_effect_only_safe_expr(Expr, _) :-
    var(Expr), !.
he_effect_only_safe_expr(Expr, _) :-
    atomic(Expr), !.
he_effect_only_safe_expr([if, Cond, Then, Else], Stack) :-
    !,
    he_effect_only_safe_arg_expr(Cond, Stack),
    he_effect_only_safe_expr(Then, Stack),
    he_effect_only_safe_expr(Else, Stack).
he_effect_only_safe_expr([if, Cond, Then], Stack) :-
    !,
    he_effect_only_safe_arg_expr(Cond, Stack),
    he_effect_only_safe_expr(Then, Stack).
he_effect_only_safe_expr([case, KeyExpr, Pairs], Stack) :-
    !,
    he_effect_only_safe_query_expr(KeyExpr, Stack),
    he_effect_only_safe_case_pairs(Pairs, Stack).
he_effect_only_safe_expr([let, Pat, Val, In], Stack) :-
    !,
    he_var_unused_in_expr(Pat, In),
    he_effect_only_safe_expr(Val, Stack),
    he_effect_only_safe_expr(In, Stack).
he_effect_only_safe_expr([chain, Val, Pat, In], Stack) :-
    !,
    he_var_unused_in_expr(Pat, In),
    he_effect_only_safe_expr(Val, Stack),
    he_effect_only_safe_expr(In, Stack).
he_effect_only_safe_expr(['let*', Binds, Body], Stack) :-
    !,
    letstar_to_rec_let(Binds, Body, RecLet),
    he_effect_only_safe_expr(RecLet, Stack).
he_effect_only_safe_expr([Head|Args], Stack) :-
    atom(Head), !,
    he_effect_only_safe_call(Head, Args, Stack).
he_effect_only_safe_expr([Head|Args], Stack) :-
    maplist({Stack}/[Item]>>he_effect_only_safe_expr(Item, Stack),
            [Head|Args]).

he_effect_only_safe_call(Head, Args, Stack) :-
    memberchk(Head, ['add-atom', 'remove-atom']), !,
    maplist({Stack}/[Arg]>>he_effect_only_safe_arg_expr(Arg, Stack), Args).
he_effect_only_safe_call(empty, [], _) :- !.
he_effect_only_safe_call(Head, Args, Stack) :-
    length(Args, Arity),
    maplist({Stack}/[Arg]>>he_effect_only_safe_arg_expr(Arg, Stack), Args),
    he_effect_only_safe_fun_1(Head, Arity, Stack).

he_effect_only_safe_case_pairs([], _).
he_effect_only_safe_case_pairs([[Pattern, Body]|Rest], Stack) :-
    he_effect_only_safe_arg_expr(Pattern, Stack),
    he_effect_only_safe_expr(Body, Stack),
    he_effect_only_safe_case_pairs(Rest, Stack).

he_effect_only_eval_arg(Arg, Eval) :-
    is_list(Arg), !,
    State = state(no_success),
    ( he_eval_or_reduce(Arg, Eval),
      nb_setarg(1, State, success)
    ; arg(1, State, no_success),
      Eval = Arg
    ).
he_effect_only_eval_arg(Arg, Arg).

he_effect_only_eval_args([], []).
he_effect_only_eval_args([Arg|Args], [Eval|Evals]) :-
    he_effect_only_eval_arg(Arg, Eval),
    he_effect_only_eval_args(Args, Evals).

he_effect_only_self_add_atom_expr(['add-atom', '&self', Term], Term).

he_effect_only_plain_self_data_atom([=, [Fun|_], _]) :-
    atom(Fun), !,
    fail.
he_effect_only_plain_self_data_atom(_).

he_collect_effect_only_self_add_atom_batch([let, Pat, Val, In], [Term|Terms], Rest) :-
    he_var_unused_in_expr(Pat, In),
    he_effect_only_self_add_atom_expr(Val, Term),
    he_collect_effect_only_self_add_atom_batch_1(In, Terms, Rest),
    Terms = [_|_].

he_collect_effect_only_self_add_atom_batch_1([let, Pat, Val, In], [Term|Terms], Rest) :-
    he_var_unused_in_expr(Pat, In),
    he_effect_only_self_add_atom_expr(Val, Term), !,
    he_collect_effect_only_self_add_atom_batch_1(In, Terms, Rest).
he_collect_effect_only_self_add_atom_batch_1(Rest, [], Rest).

he_effect_only_add_self_atom_batch(Terms) :-
    he_effect_only_eval_args(Terms, EvalTerms),
    he_effect_only_add_evaluated_self_atom_batch(EvalTerms).

he_effect_only_add_evaluated_self_atom_batch(EvalTerms) :-
    he_perf_counter_inc(effect_only_self_add_atom_batches),
    length(EvalTerms, Count),
    he_perf_counter_add(effect_only_self_add_atom_batch_terms, Count),
    forall(member(EvalTerm, EvalTerms),
           add_sexp('&self', EvalTerm)),
    ( maplist(he_effect_only_plain_self_data_atom, EvalTerms)
    -> he_perf_counter_inc(effect_only_self_add_atom_data_count_batches),
       he_perf_counter_add(effect_only_self_add_atom_data_count_batch_terms, Count),
       he_note_space_data_fact_added_batch('&self', EvalTerms)
    ;  forall(member(EvalTerm, EvalTerms),
              he_note_space_fact_added('&self', EvalTerm))
    ).

he_effect_only_expr(Expr) :-
    he_perf_counter_inc(effect_only_expr_calls),
    he_effect_only_expr_1(Expr).

he_effect_only_expr_1(Expr) :-
    var(Expr), !.
he_effect_only_expr_1(Expr) :-
    atomic(Expr), !.
he_effect_only_expr_1([if, Cond, Then, Else]) :-
    !,
    he_eval_or_reduce(Cond, Cv),
    ( Cv == true
    -> he_effect_only_expr(Then)
    ;  he_effect_only_expr(Else)
    ).
he_effect_only_expr_1([if, Cond, Then]) :-
    !,
    he_eval_or_reduce(Cond, Cv),
    ( Cv == true
    -> he_effect_only_expr(Then)
    ;  true
    ).
he_effect_only_expr_1([case, KeyExpr, Pairs]) :-
    !,
    he_effect_only_case(KeyExpr, Pairs).
he_effect_only_expr_1([let, Pat, Val, In]) :-
    !,
    he_var_unused_in_expr(Pat, In),
    ( he_collect_effect_only_self_add_atom_batch([let, Pat, Val, In], Terms, Rest)
    -> he_effect_only_add_self_atom_batch(Terms),
       he_effect_only_expr(Rest)
    ;  he_effect_only_expr(Val),
       he_effect_only_expr(In)
    ).
he_effect_only_expr_1([chain, Val, Pat, In]) :-
    !,
    he_var_unused_in_expr(Pat, In),
    he_effect_only_expr(Val),
    he_effect_only_expr(In).
he_effect_only_expr_1(['let*', Binds, Body]) :-
    !,
    letstar_to_rec_let(Binds, Body, RecLet),
    he_effect_only_expr(RecLet).
he_effect_only_expr_1([Head|Args]) :-
    atom(Head), !,
    he_effect_only_call(Head, Args).
he_effect_only_expr_1([Head|Args]) :-
    maplist(he_effect_only_expr, [Head|Args]).

he_effect_only_call(Head, Args) :-
    memberchk(Head, ['add-atom', 'remove-atom']), !,
    he_effect_only_eval_args(Args, EvalArgs),
    once(he_eval_or_reduce([Head|EvalArgs], _)).
he_effect_only_call(empty, []) :- !.
he_effect_only_call(Head, Args) :-
    length(Args, Arity),
    he_effect_only_native_plan(Head, Arity, Plan),
    Plan \== none,
    he_perf_counter_inc(effect_only_fun_direct_hits),
    he_perf_counter_inc(effect_only_native_fun_hits),
    he_effect_only_eval_args(Args, EvalArgs),
    he_effect_only_native_call(Plan, EvalArgs), !.
he_effect_only_call(Head, Args) :-
    length(Args, Arity),
    he_effect_only_safe_fun(Head, Arity), !,
    he_perf_counter_inc(effect_only_fun_direct_hits),
    he_effect_only_eval_args(Args, EvalArgs),
    once(he_eq_fact(Head, Arity, HeadArgs0, Body0)),
    copy_term(HeadArgs0-Body0, HeadArgs-Body),
    HeadArgs = EvalArgs,
    once(he_effect_only_expr(Body)).

he_effect_only_case(KeyExpr, Pairs) :-
    translate_expr_to_conj(KeyExpr, KeyConj, KeyValue),
    ( call(KeyConj),
      he_effect_only_case_pairs(Pairs, KeyValue),
      fail
    ; true
    ).

he_effect_only_case_pairs([], _).
he_effect_only_case_pairs([[Pattern, Body]|Rest], KeyValue) :-
    ( he_effect_only_case_pattern_matches(Pattern, KeyValue)
    -> he_effect_only_expr(Body)
    ;  he_effect_only_case_pairs(Rest, KeyValue)
    ).

he_effect_only_case_pattern_matches(Pattern, KeyValue) :-
    he_constrain_args(Pattern, PatternValue, PatternGoals),
    call_goals(PatternGoals),
    KeyValue = PatternValue.

he_effect_only_native_call(self_add_branching(Rel, AddOps, RecurOps), [Term, Depth]) :-
    integer(Depth),
    Depth >= 0,
    he_effect_only_native_self_add_branching(Rel, AddOps, RecurOps, Term, Depth).

he_effect_only_native_self_add_branching(_Rel, _AddOps, _RecurOps, _Term, 0) :- !.
he_effect_only_native_self_add_branching(Rel, AddOps, RecurOps, Term, Depth) :-
    Depth > 0,
    he_perf_counter_inc(effect_only_native_branching_calls),
    findall([Rel, [Op, Term]], member(Op, AddOps), Terms),
    he_effect_only_add_evaluated_self_atom_batch(Terms),
    NextDepth is Depth - 1,
    he_effect_only_native_self_add_branching_children(RecurOps, RecurOps, Rel, AddOps, Term, NextDepth).

he_effect_only_native_self_add_branching_children([], _FullRecurOps, _Rel, _AddOps, _Term, _Depth).
he_effect_only_native_self_add_branching_children([Op|Ops], FullRecurOps, Rel, AddOps, Term, Depth) :-
    NextTerm = [Op, Term],
    he_effect_only_native_self_add_branching(Rel, AddOps, FullRecurOps, NextTerm, Depth),
    he_effect_only_native_self_add_branching_children(Ops, FullRecurOps, Rel, AddOps, Term, Depth).

he_capture_bound_call_out(Call, Out, BoundCall, BoundOut) :-
    term_variables(Call-Out, Vars),
    ( Vars == []
    -> BoundCall = Call,
       BoundOut = Out
    ;  copy_term(Call-Out, BoundCall-BoundOut)
    ).

he_compiled_equation_note_result(Pair, State) :-
    Pair = _-Candidate,
    arg(4, State, RawCount0),
    RawCount is RawCount0 + 1,
    nb_setarg(4, State, RawCount),
    ( he_visible_result(Candidate)
    -> arg(5, State, VisibleCount0),
       VisibleCount is VisibleCount0 + 1,
       nb_setarg(5, State, VisibleCount),
       arg(1, State, Mode),
       ( Mode == no_visible
       -> nb_setarg(1, State, visible),
          nb_setarg(2, State, [])
       ;  true
       ),
       arg(3, State, VisibleAcc0),
       nb_setarg(3, State, [Pair|VisibleAcc0])
    ; arg(1, State, no_visible)
    -> arg(2, State, RawAcc0),
       nb_setarg(2, State, [Pair|RawAcc0])
    ;  true
    ).

he_finalize_compiled_equation_goal_results(Call, State, VisibleResults, RawResults) :-
    arg(4, State, RawCount),
    he_perf_counter_add(compiled_equation_goal_raw_rows, RawCount),
    arg(5, State, VisibleCount),
    he_perf_counter_add(compiled_equation_goal_visible_rows, VisibleCount),
    arg(3, State, VisibleAcc),
    arg(2, State, RawAcc),
    ( he_single_equation_call(Call)
    -> VisibleResults = VisibleAcc
    ;  reverse(VisibleAcc, VisibleResults)
    ),
    reverse(RawAcc, RawResults).

he_compiled_equation_goal_results(Call, Goal, Out, VisibleResults, RawResults) :-
    he_perf_counter_inc(compiled_equation_goal_result_collections),
    State = state(no_visible, [], [], 0, 0),
    ( catch(( call(Goal),
              he_capture_bound_call_out(Call, Out, BoundCall, BoundOut),
              he_compiled_equation_note_result(BoundCall-BoundOut, State),
              fail
            ),
            _,
            fail)
    ; he_finalize_compiled_equation_goal_results(Call, State, VisibleResults, RawResults)
    ).

he_note_single_equation_collecting_result(Pair, State) :-
    Pair = _-Candidate,
    arg(1, State, Mode),
    ( he_visible_result(Candidate)
    -> arg(6, State, VisibleCount0),
       VisibleCount is VisibleCount0 + 1,
       nb_setarg(6, State, VisibleCount),
       ( Mode == no_visible
       -> nb_setarg(1, State, visible),
          nb_setarg(3, State, [])
       ;  true
       ),
       arg(4, State, VisibleAcc0),
       nb_setarg(4, State, [Pair|VisibleAcc0])
    ; Mode == no_visible
    -> arg(3, State, RawAcc0),
       nb_setarg(3, State, [Pair|RawAcc0])
    ;  true
    ).

he_note_single_equation_result(Pair, State) :-
    Pair = _-Candidate,
    arg(5, State, RawCount0),
    RawCount is RawCount0 + 1,
    nb_setarg(5, State, RawCount),
    arg(1, State, Mode0),
    ( he_visible_result(Candidate) -> Visible = true ; Visible = false ),
    he_note_single_equation_result_1(Mode0, Visible, Pair, State).

he_note_single_equation_result_1(empty, true, Pair, State) :-
    nb_setarg(1, State, single_visible),
    nb_setarg(2, State, Pair).
he_note_single_equation_result_1(empty, false, Pair, State) :-
    nb_setarg(1, State, single_raw),
    nb_setarg(2, State, Pair).
he_note_single_equation_result_1(single_visible, true, Pair, State) :-
    arg(2, State, FirstPair),
    arg(6, State, VisibleCount0),
    VisibleCount is VisibleCount0 + 1,
    nb_setarg(6, State, VisibleCount),
    nb_setarg(1, State, visible),
    nb_setarg(2, State, none),
    nb_setarg(4, State, [Pair, FirstPair]).
he_note_single_equation_result_1(single_visible, false, _Pair, State) :-
    arg(2, State, FirstPair),
    arg(6, State, VisibleCount0),
    VisibleCount is VisibleCount0 + 1,
    nb_setarg(6, State, VisibleCount),
    nb_setarg(1, State, visible),
    nb_setarg(2, State, none),
    nb_setarg(4, State, [FirstPair]).
he_note_single_equation_result_1(single_raw, true, Pair, State) :-
    arg(6, State, VisibleCount0),
    VisibleCount is VisibleCount0 + 1,
    nb_setarg(6, State, VisibleCount),
    nb_setarg(1, State, visible),
    nb_setarg(2, State, none),
    nb_setarg(3, State, []),
    nb_setarg(4, State, [Pair]).
he_note_single_equation_result_1(single_raw, false, Pair, State) :-
    arg(2, State, FirstPair),
    nb_setarg(1, State, no_visible),
    nb_setarg(2, State, none),
    nb_setarg(3, State, [Pair, FirstPair]),
    nb_setarg(4, State, []).
he_note_single_equation_result_1(no_visible, _Visible, Pair, State) :-
    he_note_single_equation_collecting_result(Pair, State).
he_note_single_equation_result_1(visible, _Visible, Pair, State) :-
    he_note_single_equation_collecting_result(Pair, State).

he_finalize_single_equation_goal_result(State, Resolution) :-
    arg(5, State, RawCount),
    he_perf_counter_add(compiled_equation_goal_raw_rows, RawCount),
    arg(6, State, VisibleCount),
    he_perf_counter_add(compiled_equation_goal_visible_rows, VisibleCount),
    arg(1, State, Mode),
    ( Mode == empty
    -> Resolution = none
    ; Mode == single_visible
    -> arg(2, State, Pair),
       Resolution = single(Pair)
    ; Mode == single_raw
    -> arg(2, State, Pair),
       Resolution = single(Pair)
    ; Mode == no_visible
    -> arg(3, State, RawAcc),
       reverse(RawAcc, RawResults),
       Resolution = collect([], RawResults)
    ; Mode == visible
    -> arg(4, State, VisibleAcc),
       reverse(VisibleAcc, VisibleResults),
       Resolution = collect(VisibleResults, [])
    ).

he_single_equation_goal_result(Call, Goal, Out, Resolution) :-
    he_perf_counter_inc(compiled_equation_goal_single_result_calls),
    State = state(empty, none, [], [], 0, 0),
    ( catch(( call(Goal),
              he_capture_bound_call_out(Call, Out, BoundCall, BoundOut),
              he_note_single_equation_result(BoundCall-BoundOut, State),
              fail
            ),
            _,
            fail)
    ; true
    ),
    he_finalize_single_equation_goal_result(State, Resolution).

he_note_compiled_equation_first_visible_result(Pair, State, Stop) :-
    Pair = _-Candidate,
    arg(3, State, RawCount0),
    RawCount is RawCount0 + 1,
    nb_setarg(3, State, RawCount),
    ( he_visible_result(Candidate)
    -> arg(4, State, VisibleCount0),
       VisibleCount is VisibleCount0 + 1,
       nb_setarg(4, State, VisibleCount),
       arg(2, State, VisiblePair0),
       ( VisiblePair0 == none
       -> nb_setarg(2, State, Pair)
       ;  true
       ),
       Stop = true
    ;  arg(1, State, RawPair0),
       ( RawPair0 == none
       -> nb_setarg(1, State, Pair)
       ;  true
       ),
       Stop = false
    ).

he_finalize_compiled_equation_goal_first_visible(State, BoundCall, BoundOut) :-
    arg(3, State, RawCount),
    he_perf_counter_add(compiled_equation_goal_first_visible_raw_rows, RawCount),
    arg(4, State, VisibleCount),
    he_perf_counter_add(compiled_equation_goal_first_visible_visible_rows, VisibleCount),
    ( arg(2, State, BoundCall-BoundOut),
      BoundCall \== none
    -> true
    ; arg(1, State, BoundCall-BoundOut),
      BoundCall \== none
    ).

he_compiled_equation_goal_first_visible_result(Call, Goal, Out, BoundCall, BoundOut) :-
    he_perf_counter_inc(compiled_equation_goal_first_visible_calls),
    State = state(none, none, 0, 0),
    ( catch(( call(Goal),
              he_capture_bound_call_out(Call, Out, ProbeCall, ProbeOut),
              he_note_compiled_equation_first_visible_result(ProbeCall-ProbeOut, State, Stop),
              Stop == true
            ),
            _,
            fail)
    -> true
    ;  true
    ),
    he_finalize_compiled_equation_goal_first_visible(State, BoundCall, BoundOut).

he_multi_equation_direct_plan(Fun, Arity, Plan) :-
    he_multi_equation_direct_plan_cache(Fun, Arity, Plan), !.
he_multi_equation_direct_plan(Fun, Arity, Plan) :-
    ( he_multi_equation_direct_plan_1(Fun, Arity, Plan0)
    -> Plan = Plan0
    ;  Plan = none
    ),
    assertz(he_multi_equation_direct_plan_cache(Fun, Arity, Plan)).

he_multi_equation_direct_plan_1(Fun, Arity, safe(Uses)) :-
    atom(Fun),
    \+ he_single_equation_arity(Fun, Arity),
    metta_user_functor(Fun, UserFun),
    OutArity is Arity + 1,
    findall(HeadArgs-Body,
            ( functor(Head, UserFun, OutArity),
              clause(Head, Body),
              Head =.. [_|AllArgs],
              append(HeadArgs, [_Out], AllArgs)
            ),
            Clauses),
    Clauses \= [],
    he_multi_equation_clause_set_safe(Fun, Clauses, Uses0),
    Uses0 \= [],
    sort(Uses0, Uses).

he_multi_equation_clause_set_safe(Fun, Clauses, Uses) :-
    findall(Use,
            ( member(HeadArgs-Body, Clauses),
              he_multi_equation_clause_safe(Fun, HeadArgs, Body, ClauseUses),
              member(Use, ClauseUses)
            ),
            Uses).

he_multi_equation_clause_safe(_Fun, _HeadArgs, true, []) :- !.
he_multi_equation_clause_safe(Fun, HeadArgs, Body, Uses) :-
    he_multi_equation_body_safe(Body, Fun, HeadArgs, Uses).

he_multi_equation_body_safe((Left, Right), Fun, HeadArgs, Uses) :-
    !,
    he_multi_equation_body_safe(Left, Fun, HeadArgs, LeftUses),
    he_multi_equation_body_safe(Right, Fun, HeadArgs, RightUses),
    append(LeftUses, RightUses, Uses).
he_multi_equation_body_safe((Cond -> Then ; Else), Fun, HeadArgs, Uses) :-
    !,
    he_multi_equation_body_safe(Cond, Fun, HeadArgs, CondUses),
    he_multi_equation_body_safe(Then, Fun, HeadArgs, ThenUses),
    he_multi_equation_body_safe(Else, Fun, HeadArgs, ElseUses),
    append(CondUses, ThenUses, Uses0),
    append(Uses0, ElseUses, Uses).
he_multi_equation_body_safe((Cond -> Then), Fun, HeadArgs, Uses) :-
    !,
    he_multi_equation_body_safe(Cond, Fun, HeadArgs, CondUses),
    he_multi_equation_body_safe(Then, Fun, HeadArgs, ThenUses),
    append(CondUses, ThenUses, Uses).
he_multi_equation_body_safe(Goal, _Fun, _HeadArgs, []) :-
    nonvar(Goal),
    Goal = (_ = _), !.
he_multi_equation_body_safe(Goal, _Fun, _HeadArgs, []) :-
    nonvar(Goal),
    Goal = (_ == _), !.
he_multi_equation_body_safe(Goal, _Fun, _HeadArgs, []) :-
    nonvar(Goal),
    Goal = (_ \== _), !.
he_multi_equation_body_safe(cons(_, _, _), _Fun, _HeadArgs, []) :- !.
he_multi_equation_body_safe('is-expr'(_, _), _Fun, _HeadArgs, []) :- !.
he_multi_equation_body_safe(he_call_typed(Head, _Args, _Types, _Out),
                            _Fun, _HeadArgs, []) :-
    memberchk(Head, [==, '!=', '<', '>', '<=', '>=', '+', '-', '*', '/', '%']),
    !.
he_multi_equation_body_safe(he_call_compiled_or_self(Call, _Goal, _Out),
                            Fun, _HeadArgs, []) :-
    nonvar(Call),
    Call = [Fun|_], !.
he_multi_equation_body_safe(he_call_compiled_equation_or_self(Call, _Goal, _Out),
                            Fun, _HeadArgs, []) :-
    nonvar(Call),
    Call = [Fun|_], !.
he_multi_equation_body_safe(he_dynamic_var_head_call_raw(HeadVar, RawArgs, _Out),
                            _Fun, HeadArgs, [use(Pos, ArgCount)]) :-
    var(HeadVar),
    he_multi_equation_head_arg_position(HeadArgs, HeadVar, Pos),
    is_list(RawArgs),
    length(RawArgs, ArgCount), !.

he_multi_equation_head_arg_position(HeadArgs, Var, Pos) :-
    nth1(Pos, HeadArgs, Arg),
    Arg == Var.

he_multi_equation_callable_uses_safe([], _Args).
he_multi_equation_callable_uses_safe([use(Pos, ArgCount)|Uses], Args) :-
    nth1(Pos, Args, Callable),
    he_multi_equation_callable_safe(Callable, ArgCount),
    he_multi_equation_callable_uses_safe(Uses, Args).

he_multi_equation_callable_safe(Callable, ArgCount) :-
    nonvar(Callable),
    Callable = partial(Fun, Bound),
    atom(Fun),
    length(Bound, BoundCount),
    Supplied is BoundCount + ArgCount,
    OutArity is Supplied + 1,
    he_partial_apply_dispatch_plan(Fun, OutArity, runtime_predicate), !.
he_multi_equation_callable_safe(Callable, ArgCount) :-
    atom(Callable),
    \+ he_space_ref_atom(Callable),
    OutArity is ArgCount + 1,
    he_runtime_direct_predicate_plan(Callable, OutArity, runtime_predicate).

he_multi_equation_shape_direct_call(Call, Goal, Out) :-
    Call = [Fun|Args],
    atom(Fun),
    length(Args, Arity),
    he_multi_equation_direct_plan(Fun, Arity, safe(Uses)),
    he_multi_equation_callable_uses_safe(Uses, Args),
    he_perf_counter_inc(compiled_equation_goal_multi_shape_calls),
    once(( call(Goal),
           he_capture_bound_call_out(Call, Out, BoundCall, BoundOut)
         )),
    he_perf_counter_inc(compiled_equation_goal_multi_shape_hits),
    he_perf_counter_add(compiled_equation_goal_raw_rows, 1),
    ( he_visible_result(BoundOut)
    -> he_perf_counter_add(compiled_equation_goal_visible_rows, 1)
    ;  true
    ),
    Call = BoundCall,
    Out = BoundOut.

he_call_compiled_equation_first_visible(Call, Goal, Out) :-
    he_single_equation_call(Call), !,
    once(he_call_compiled_or_self(Call, Goal, Out)).
he_call_compiled_equation_first_visible(Call, Goal, Out) :-
    he_compiled_equation_goal_first_visible_result(Call, Goal, Out, BoundCall, BoundOut),
    Call = BoundCall,
    Out = BoundOut.

he_build_compiled_equation_first_visible(Call, Out, Goal) :-
    he_profile_enabled,
    nonvar(Call),
    is_list(Call),
    he_build_native_contract_first_visible_goal(Call, Out, DirectGoal), !,
    Goal = once(DirectGoal).
he_build_compiled_equation_first_visible(Call, Out, Goal) :-
    he_profile_enabled,
    nonvar(Call),
    is_list(Call),
    he_compiled_equation_goal(Call, Out, CompiledGoal), !,
    Goal = he_call_compiled_equation_first_visible(Call, CompiledGoal, Out).

he_call_compiled_equation_or_self([iterate, I, N, State, Step], _Goal, Out) :-
    he_profile_enabled,
    integer(I),
    integer(N),
    N >= 0, !,
    he_native_iterate(I, N, State, Step, Out).
he_call_compiled_equation_or_self(Call, _Goal, Out) :-
    he_profile_enabled,
    he_build_native_queue_search_goal(Call, Out, DirectGoal), !,
    call(DirectGoal).
he_call_compiled_equation_or_self(Call, Goal, Out) :-
    he_single_result_compiled_call_or_self(Call, Goal, Out), !.
he_call_compiled_equation_or_self(Call, Goal, Out) :-
    he_single_equation_call(Call), !,
    he_single_equation_goal_result(Call, Goal, Out, Resolution),
    ( Resolution = single(BoundCall-BoundOut)
    -> he_perf_counter_inc(compiled_equation_goal_single_direct_hits),
       Call = BoundCall,
       Out = BoundOut
    ; Resolution = collect(VisibleResults, RawResults)
    -> he_perf_counter_inc(compiled_equation_goal_single_collect_fallbacks),
       ( VisibleResults \= []
       -> member(BoundCall-BoundOut, VisibleResults)
       ; member(BoundCall-BoundOut, RawResults)
       ),
       Call = BoundCall,
       Out = BoundOut
    ).
he_call_compiled_equation_or_self(Call, Goal, Out) :-
    he_multi_equation_shape_direct_call(Call, Goal, Out), !.
he_call_compiled_equation_or_self(Call, Goal, Out) :-
    he_compiled_equation_goal_results(Call, Goal, Out, VisibleResults, RawResults),
    ( VisibleResults \= []
    -> member(BoundCall-BoundOut, VisibleResults),
       Call = BoundCall,
       Out = BoundOut
    ; member(BoundCall-BoundOut, RawResults),
      Call = BoundCall,
      Out = BoundOut
    ).
he_call_compiled_or_self(Call, Goal, Out) :-
    he_call_has_equation(Call), !,
    he_call_compiled_equation_or_self(Call, Goal, Out).
he_call_compiled_or_self(Call, Goal, Out) :-
    State = state(no_solution),
    ( catch((call(Goal), nb_setarg(1, State, solved)), _, fail)
    ; arg(1, State, no_solution),
      he_retry_compiled_call_with_evaluated_args(Call, Out),
      nb_setarg(1, State, solved)
    ; arg(1, State, no_solution),
      Out = Call
    ).

he_retry_compiled_call_with_evaluated_args([Fun|Args], Out) :-
    he_profile_enabled,
    atom(Fun),
    he_eval_runtime_args(Args, EvalArgs),
    EvalArgs \=@= Args,
    he_compiled_user_goal([Fun|EvalArgs], Out, EvalGoal),
    catch(call(EvalGoal), _, fail).

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
    he_eval_or_reduce([Func, X], Y),
    he_maplist_reduce(Xs, Func, Ys).

he_filterlist_reduce([], _Func, []).
he_filterlist_reduce([X|Xs], Func, Out) :-
    he_eval_or_reduce([Func, X], Keep),
    he_filterlist_reduce(Xs, Func, Rest),
    ( (Keep == true ; Keep == 'True')
    -> Out = [X|Rest]
    ;  Out = Rest
    ).

he_native_iterate(_I, 0, State, _Step, State) :- !.
he_native_iterate(I, N, State, Step, Out) :-
    atom(Step),
    he_compiled_goal_user_functor(Step, 3, UserFun), !,
    he_native_iterate_compiled(UserFun, I, N, State, Out).
he_native_iterate(I, N, State0, Step, Out) :-
    N > 0,
    once(he_eval_or_reduce([Step, I, State0], State1)),
    I1 is I + 1,
    N1 is N - 1,
    he_native_iterate(I1, N1, State1, Step, Out).

he_native_iterate_compiled(_UserFun, _I, 0, State, State) :- !.
he_native_iterate_compiled(UserFun, I, N, State0, Out) :-
    N > 0,
    once(call(UserFun, I, State0, State1)),
    I1 is I + 1,
    N1 is N - 1,
    he_native_iterate_compiled(UserFun, I1, N1, State1, Out).

he_foldl_reduce([], _Func, Acc, Acc).
he_foldl_reduce([X|Xs], Func, Acc0, Out) :-
    he_eval_or_reduce([Func, X, Acc0], Acc1),
    he_foldl_reduce(Xs, Func, Acc1, Out).
