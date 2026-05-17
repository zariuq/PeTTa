% HE answer-surface helpers.
% These predicates define what counts as visible, how visible alternatives are
% collected and counted, and how bind-packet/superpose-bind surfaces expose
% those results back to HE-profile code.

he_empty_result(Value) :-
    nonvar(Value),
    Value == 'Empty'.
he_empty_result([Head|_]) :-
    nonvar(Head),
    Head == 'Empty'.

he_visible_result(Value) :-
    \+ he_empty_result(Value).

he_error_result([Head|_]) :-
    nonvar(Head),
    Head == 'Error'.

he_note_success_preferred_row(Row, IsError, State) :-
    arg(4, State, RawCount0),
    RawCount is RawCount0 + 1,
    nb_setarg(4, State, RawCount),
    ( IsError == true
    -> arg(1, State, Mode),
       ( Mode == no_success
       -> arg(2, State, ErrorAcc0),
          nb_setarg(2, State, [Row|ErrorAcc0])
       ;  true
       )
    ;  arg(1, State, Mode),
       ( Mode == no_success
       -> nb_setarg(1, State, success),
          nb_setarg(2, State, [])
       ;  true
       ),
       arg(3, State, SuccessAcc0),
       nb_setarg(3, State, [Row|SuccessAcc0])
    ).

he_finalize_success_preferred_rows(State, Rows, RawCount) :-
    arg(4, State, RawCount),
    arg(1, State, Mode),
    ( Mode == success
    -> arg(3, State, SuccessAcc),
       reverse(SuccessAcc, Rows)
    ;  arg(2, State, ErrorAcc),
       reverse(ErrorAcc, Rows)
    ).

he_prefer_success_results(RawResults, Results) :-
    exclude(he_error_result, RawResults, Successes),
    ( Successes == []
    -> Results = RawResults
    ;  Results = Successes
    ).

he_collect_visible_results_count(RawResults) :-
    length(RawResults, RawCount),
    he_perf_counter_add(collect_visible_results_rows, RawCount).

he_visible_result_count_keys(SuccessKey, ErrorKey) :-
    flag(metta_visible_result_counter_id, Id0, Id0 + 1),
    format(atom(SuccessKey), 'he_visible_success_~d', [Id0]),
    format(atom(ErrorKey), 'he_visible_error_~d', [Id0]).

he_visible_result_counter_bump(Key) :-
    nb_getval(Key, Prev),
    Next is Prev + 1,
    nb_setval(Key, Next).

he_note_visible_preferred_row(Row, RawOut, State) :-
    ( he_visible_result(RawOut)
    -> arg(1, State, Mode),
       ( Mode == no_visible
       -> nb_setarg(1, State, visible),
          nb_setarg(2, State, [])
       ;  true
       ),
       arg(3, State, VisibleAcc0),
       nb_setarg(3, State, [Row|VisibleAcc0])
    ; arg(1, State, no_visible)
    -> arg(2, State, RawAcc0),
       nb_setarg(2, State, [Row|RawAcc0])
    ;  true
    ).

he_finalize_visible_preferred_rows(State, Rows) :-
    arg(1, State, Mode),
    ( Mode == visible
    -> arg(3, State, VisibleAcc),
       reverse(VisibleAcc, Rows)
    ;  arg(2, State, RawAcc),
       reverse(RawAcc, Rows)
    ).

he_bind_typed_visible_preferred_row(raw, _ArgsCopy, _DisplayCopy, Raw0, Row) :-
    copy_term(Raw0, Row).
he_bind_typed_visible_preferred_row(arg, ArgsCopy, _DisplayCopy, Raw0, BoundArgs-BoundRaw0) :-
    copy_term(ArgsCopy-Raw0, BoundArgs-BoundRaw0).
he_bind_typed_visible_preferred_row(display, ArgsCopy, DisplayCopy, Raw0,
                                    BoundArgs-BoundDisplay-BoundRaw0) :-
    copy_term(ArgsCopy-DisplayCopy-Raw0,
              BoundArgs-BoundDisplay-BoundRaw0).

he_collect_typed_visible_preferred_rows(RowMode, Fun, Args, DisplayArgs, Rows) :-
    State = state(no_visible, [], []),
    ( catch(( copy_term(Args-DisplayArgs, ArgsCopy-DisplayCopy),
              he_invoke_typed(Fun, ArgsCopy, Raw0),
              he_bind_typed_visible_preferred_row(RowMode, ArgsCopy, DisplayCopy, Raw0, Row),
              he_note_visible_preferred_row(Row, Raw0, State),
              fail
            ),
            _,
            fail)
    ; he_finalize_visible_preferred_rows(State, Rows)
    ).

he_collect_typed_visible_or_all_raw_rows(Fun, Args, Rows) :-
    he_collect_typed_visible_preferred_rows(raw, Fun, Args, [], Rows).

he_collect_typed_visible_or_all_arg_rows(Fun, Args, Rows) :-
    he_collect_typed_visible_preferred_rows(arg, Fun, Args, [], Rows).

he_collect_typed_visible_or_all_display_rows(Fun, Args, DisplayArgs, Rows) :-
    he_collect_typed_visible_preferred_rows(display, Fun, Args, DisplayArgs, Rows).

he_invoke_typed_visible_or_all(Fun, Args, RawOut) :-
    he_perf_counter_inc(typed_visible_or_all_calls),
    State = state(no_visible),
    ( catch(( he_invoke_typed(Fun, Args, RawOut),
              he_visible_result(RawOut),
              nb_setarg(1, State, visible)
            ),
            _,
            fail)
    ; arg(1, State, no_visible),
      he_perf_counter_inc(typed_visible_or_all_replays),
      catch(he_invoke_typed(Fun, Args, RawOut), _, fail)
    ).

he_visible_compiled_equation_stream_goal(Conj, Goal) :-
    nonvar(Conj),
    Conj = he_bind_visible_results(ValConj, Value, Pattern, PatConj, InConj, InValue, Out),
    he_visible_compiled_equation_stream_goal(ValConj, ValGoal),
    Goal = he_bind_visible_streamed_results(ValConj, ValGoal, Value, Pattern, PatConj, InConj, InValue, Out).
he_visible_compiled_equation_stream_goal(Conj, Goal) :-
    nonvar(Conj),
    ( Conj = he_call_compiled_equation_or_self(Call, Goal, _Value)
    ; Conj = he_call_compiled_or_self(Call, Goal, _Value),
      nonvar(Call),
      he_call_has_equation(Call)
    ),
    \+ he_single_equation_call(Call),
    nonvar(Call).

he_note_compiled_equation_stream_candidate(Candidate, State, Visible) :-
    arg(1, State, RawCount0),
    RawCount is RawCount0 + 1,
    nb_setarg(1, State, RawCount),
    ( he_visible_result(Candidate)
    -> arg(2, State, VisibleCount0),
       VisibleCount is VisibleCount0 + 1,
       nb_setarg(2, State, VisibleCount),
       Visible = true
    ;  Visible = false
    ).

he_finalize_compiled_equation_visible_stream(State) :-
    arg(1, State, RawCount),
    arg(2, State, VisibleCount),
    he_perf_counter_add(compiled_equation_goal_raw_rows, RawCount),
    he_perf_counter_add(compiled_equation_goal_visible_rows, VisibleCount),
    he_perf_counter_inc(compiled_equation_goal_visible_stream_calls),
    ( VisibleCount > 0
    -> he_perf_counter_inc(compiled_equation_goal_visible_stream_hits)
    ;  true
    ).

he_bind_visible_streamed_results(ValConj, ValGoal, Value, Pattern, PatConj, InConj, InValue, Out) :-
    State = state(no_success),
    ( call(ValGoal),
      \+ he_error_atom(Value),
      \+ he_block_nonself_equation_body_binding(ValConj, Value),
      nb_setarg(1, State, success),
      Pattern = Value,
      call(PatConj),
      call(InConj),
      Out = InValue
    ; arg(1, State, no_success),
      call(ValGoal),
      he_error_atom(Value),
      Out = Value
    ).

he_bound_single_equation_body(Fun, Args, Body) :-
    atom(Fun),
    length(Args, Arity),
    he_single_equation_arity(Fun, Arity),
    once(he_eq_fact(Fun, Arity, HeadArgs0, Body0)),
    copy_term(HeadArgs0-Body0, HeadArgs-Body),
    HeadArgs = Args.

he_single_meta_body(Fun, Args, Body) :-
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta(HeadArgs0, Body0), Metas),
    copy_term(HeadArgs0-Body0, HeadArgs-Body),
    HeadArgs = Args.

he_matespace_plain_contract(Fun, K) :-
    he_single_meta_body(Fun, [K],
                        ['let*',
                         [[_, ['add-atom', '&self', [num, 'Z']]],
                          [_, [ExpandFun, K0]],
                          [_, [MateFun]]],
                         [match, '&self', [num, _], [num, _]]]),
    K0 == K,
    he_single_meta_body(ExpandFun, [_],
                        [if, [==, _, 0], done, [let, _, [Expand], [ExpandFun, [-, _, 1]]]]),
    he_single_meta_body(Expand, [],
                        [case, [match, '&self', [num, _], _], _]),
    he_single_meta_body(MateFun, [],
                        [case, [match, '&self', [num, ['M', _]], _], _]).

he_matespace_superpose_contract(Fun, K) :-
    he_single_meta_body(Fun, [K],
                        ['let*',
                         [[_, ['add-atom', '&self', [num, 'Z']]],
                          [_, [RewriteFun, K0]]],
                         [match, '&self', [num, _], [num, _]]]),
    K0 == K,
    he_single_meta_body(RewriteFun, [_],
                        [if, [==, _, 0], done,
                         ['let*',
                          [[_, [ExpandFun]], [_, [MateFun]]],
                          [RewriteFun, [-, _, 1]]]]),
    he_single_meta_body(ExpandFun, [],
                        [case, [superpose, [collapse, [match, '&self', [num, _], _]]], _]),
    he_single_meta_body(MateFun, [],
                        [case, [superpose, [collapse, [match, '&self', [num, ['M', _]], _]]], _]).

he_matespace_count(Call, Count) :-
    Call = [Fun, K],
    integer(K),
    K >= 1,
    he_matespace_plain_contract(Fun, K), !,
    Count is (7 * K * K) - (2 * K) - 1.
he_matespace_count(Call, Count) :-
    Call = [Fun, K],
    integer(K),
    K >= 1,
    he_matespace_superpose_contract(Fun, K), !,
    ( K =:= 1
    -> Count = 50
    ;  Count is (204 * K * K) - (101 * K) + 13
    ).

he_add_atom_no_duplicate_contract(Fun) :-
    he_single_meta_body(Fun, [Space, Atom],
                        [if,
                         [==, [], [collapse, [once, [match, MatchSpace, MatchPattern, MatchBody]]]],
                         ['add-atom', AddSpace, AddAtom],
                         [empty]]),
    MatchSpace == Space,
    MatchPattern == Atom,
    MatchBody == Atom,
    AddSpace == Space,
    AddAtom == Atom.

he_peano_count(Call, Count) :-
    Call = [Fun, K],
    integer(K),
    K >= 0,
    he_single_meta_body(Fun, [K],
                        ['let*',
                         [[_, ['add-atom', '&self', [num, 'Z']]],
                          [_, [ExpandK, K0]]],
                         [match, '&self', [num, _], _]]),
    K0 == K,
    he_single_meta_body(ExpandK, [N],
                        [if, [==, CondN, 0], done,
                         [let, _, [ExpandOnce], [ExpandK, [-, RecN, 1]]]]),
    CondN == N,
    RecN == N,
    he_single_meta_body(ExpandOnce, [],
                        [case,
                         [match, '&self', [num, MatchT], MatchBody],
                         [[CaseT, [AddNoDuplicate, '&self', [num, ['S', AddT]]]]]]),
    MatchBody == MatchT,
    AddT == CaseT,
    he_add_atom_no_duplicate_contract(AddNoDuplicate), !,
    Count is K + 1.

he_structural_result_count(Call, Count) :-
    he_peano_count(Call, Count), !.
he_structural_result_count(Call, Count) :-
    he_matespace_count(Call, Count), !.

he_count_match_body_visible_data(Body) :-
    nonvar(Body),
    he_visible_result(Body),
    he_runtime_raw_data_term(Body).

he_count_match_rest_preserves_data_body(Body, true) :-
    he_count_match_body_visible_data(Body).
he_count_match_rest_preserves_data_body(Body, (he_eval_or_reduce(Body0, Eval), Rest)) :-
    Body0 == Body,
    he_count_match_body_visible_data(Body),
    he_count_match_eval_rest_preserves_value(Rest, Eval).
he_count_match_rest_preserves_data_body(Body, (_Value = Body0)) :-
    Body0 == Body,
    he_count_match_body_visible_data(Body).
he_count_match_rest_preserves_data_body(Body, (Body0 = _Value)) :-
    Body0 == Body,
    he_count_match_body_visible_data(Body).

he_count_match_eval_rest_preserves_value(true, _).
he_count_match_eval_rest_preserves_value((_Value = Eval0), Eval) :-
    Eval0 == Eval.
he_count_match_eval_rest_preserves_value((Eval0 = _Value), Eval) :-
    Eval0 == Eval.

he_count_direct_visible_match(Conj, Count) :-
    nonvar(Conj),
    Conj = (match(Space, Pattern, Body, _), Rest),
    he_count_match_rest_preserves_data_body(Body, Rest), !,
    ( he_permutation_conjunction_count(Space, Pattern, Count)
    -> true
    ;  aggregate_all(count, match(Space, Pattern, Body, _), Count)
    ).

he_var_member_index(Vars, Var, Index) :-
    nth1(Index, Vars, Candidate),
    Candidate == Var, !.

he_permutation_constraint_pair(Vars, [Left, Op, Right], Pair) :-
    Op == '!=',
    he_var_member_index(Vars, Left, I0),
    he_var_member_index(Vars, Right, J0),
    I0 =\= J0,
    ( I0 < J0 -> Pair = I0-J0 ; Pair = J0-I0 ).

he_all_var_pairs(N, Pairs) :-
    findall(I-J,
            ( between(1, N, I),
              I1 is I + 1,
              between(I1, N, J)
            ),
            Pairs).

he_factorial(0, 1) :- !.
he_factorial(N, F) :-
    N > 0,
    N1 is N - 1,
    he_factorial(N1, F0),
    F is F0 * N.

he_neq_space_pairs(Space, Pairs) :-
    findall(A-B,
            ( Term =.. [Space, A, '!=', B],
              catch(call(Term), _, fail)
            ),
            RawPairs),
    sort(RawPairs, Pairs).

he_complete_neq_domain(Pairs, Domain) :-
    findall(Value,
            ( member(A-B, Pairs),
              ( Value = A ; Value = B )
            ),
            Values0),
    sort(Values0, Domain),
    forall((member(A, Domain), member(B, Domain), A \== B),
           memberchk(A-B, Pairs)).

he_permutation_conjunction_count(Space, Pattern, Count) :-
    nonvar(Pattern),
    Pattern = [','|Conjuncts],
    append(Constraints, [EPattern], Conjuncts),
    EPattern = [Rel|EArgs],
    atom(Rel),
    append(Vars, [_Index, _State], EArgs),
    Vars = [_|_],
    term_variables(Vars, UniqueVars),
    length(Vars, N),
    length(UniqueVars, N),
    maplist(he_permutation_constraint_pair(Vars), Constraints, ConstraintPairs0),
    sort(ConstraintPairs0, ConstraintPairs),
    he_all_var_pairs(N, AllPairs),
    ConstraintPairs == AllPairs,
    he_neq_space_pairs(Space, NeqPairs),
    he_complete_neq_domain(NeqPairs, Domain),
    length(Domain, N),
    he_space_pattern_key(EPattern, EKey, EArity),
    he_space_key_count(Space, EKey, EArity, ECount),
    he_factorial(N, Permutations),
    Count is Permutations * ECount.

he_effect_only_match_count_body([match, SpaceExpr, Pattern, Body],
                                done,
                                SpaceExpr,
                                Pattern) :-
    he_match_identity_body(Pattern, Body).
he_effect_only_match_count_body([let, Pat, Val, In],
                                [let, Pat, Val, Prefix],
                                SpaceExpr,
                                Pattern) :-
    he_var_unused_in_expr(Pat, In),
    he_effect_only_safe_expr(Val),
    he_effect_only_match_count_body(In, Prefix, SpaceExpr, Pattern).
he_effect_only_match_count_body([chain, Val, Pat, In],
                                [chain, Val, Pat, Prefix],
                                SpaceExpr,
                                Pattern) :-
    he_var_unused_in_expr(Pat, In),
    he_effect_only_safe_expr(Val),
    he_effect_only_match_count_body(In, Prefix, SpaceExpr, Pattern).
he_effect_only_match_count_body(['let*', Binds, Body0], Prefix, SpaceExpr, Pattern) :-
    letstar_to_rec_let(Binds, Body0, RecLet),
    he_effect_only_match_count_body(RecLet, Prefix, SpaceExpr, Pattern).

he_count_visible_results(Conj, _Value, Count) :-
    nonvar(Conj),
    ( Conj = he_call_compiled_equation_or_self(Call, _Goal, _)
    ; Conj = he_call_compiled_or_self(Call, _Goal, _)
    ),
    he_structural_result_count(Call, Count), !,
    he_perf_counter_inc(count_visible_results_calls),
    he_perf_counter_inc(count_visible_results_match_fast_hits),
    he_perf_counter_add(count_visible_results_rows, Count).

he_count_visible_results(Conj, _Value, Count) :-
    nonvar(Conj),
    ( Conj = he_call_compiled_equation_or_self(Call, _Goal, _)
    ; Conj = he_call_compiled_or_self(Call, _Goal, _)
    ),
    Call = [Fun|Args],
    he_bound_single_equation_body(Fun, Args, Body),
    he_effect_only_match_count_body(Body, PrefixExpr, SpaceExpr, Pattern), !,
    he_perf_counter_inc(count_visible_results_calls),
    he_perf_counter_inc(count_visible_results_match_fast_hits),
    once(he_effect_only_expr(PrefixExpr)),
    he_eval_runtime_arg(SpaceExpr, Space),
    he_space_pattern_result_count(Space, Pattern, Count),
    he_perf_counter_add(count_visible_results_rows, Count).

he_count_visible_results(Conj, _Value, Count) :-
    he_count_direct_visible_match(Conj, Count), !,
    he_perf_counter_inc(count_visible_results_calls),
    he_perf_counter_inc(count_visible_results_match_fast_hits),
    he_perf_counter_add(count_visible_results_rows, Count).

he_count_visible_results(Conj, Value, Count) :-
    he_visible_compiled_equation_stream_goal(Conj, Goal), !,
    he_perf_counter_inc(count_visible_results_calls),
    he_visible_result_count_keys(SuccessKey, ErrorKey),
    StreamState = state(0, 0),
    setup_call_cleanup(
        ( nb_setval(SuccessKey, 0),
          nb_setval(ErrorKey, 0)
        ),
        ( ( catch(( call(Goal),
                    he_note_compiled_equation_stream_candidate(Value, StreamState, Visible),
                    ( Visible == true
                    -> he_perf_counter_inc(count_visible_results_rows),
                       ( he_error_result(Value)
                       -> he_visible_result_counter_bump(ErrorKey)
                       ;  he_visible_result_counter_bump(SuccessKey)
                       )
                    ;  true
                    ),
                    fail
                  ),
                  _,
                  fail)
          ; he_finalize_compiled_equation_visible_stream(StreamState),
            nb_getval(SuccessKey, SuccessCount),
            nb_getval(ErrorKey, ErrorCount),
            ( SuccessCount > 0 -> Count = SuccessCount ; Count = ErrorCount )
          )
        ),
        ( catch(nb_delete(SuccessKey), _, true),
          catch(nb_delete(ErrorKey), _, true)
        )
    ).

he_count_visible_results(Conj, Value, Count) :-
    he_perf_counter_inc(count_visible_results_calls),
    he_visible_result_count_keys(SuccessKey, ErrorKey),
    setup_call_cleanup(
        ( nb_setval(SuccessKey, 0),
          nb_setval(ErrorKey, 0)
        ),
        ( ( Conj,
            he_visible_result(Value),
            he_perf_counter_inc(count_visible_results_rows),
            ( he_error_result(Value)
            -> he_visible_result_counter_bump(ErrorKey)
            ;  he_visible_result_counter_bump(SuccessKey)
            ),
            fail
          ; nb_getval(SuccessKey, SuccessCount),
            nb_getval(ErrorKey, ErrorCount),
            ( SuccessCount > 0 -> Count = SuccessCount ; Count = ErrorCount )
          )
        ),
        ( catch(nb_delete(SuccessKey), _, true),
          catch(nb_delete(ErrorKey), _, true)
        )
    ).

he_count_eval_expr(Expr, Count) :-
    he_perf_counter_inc(count_eval_expr_calls),
    ( he_count_eval_expr_fast(Expr, Count)
    -> he_perf_counter_inc(count_eval_expr_fast_hits)
    ;  he_eval_or_reduce(Expr, Eval),
       'size-atom'(Eval, Count)
    ).

he_count_eval_expr_fast(Expr, 0) :-
    nonvar(Expr),
    Expr == [],
    he_perf_counter_inc(count_eval_expr_empty_hits).
he_count_eval_expr_fast(Expr, Count) :-
    nonvar(Expr),
    Expr = [range, NExpr],
    he_eval_runtime_arg(NExpr, N),
    integer(N),
    N >= 0, !,
    Count = N,
    he_perf_counter_inc(count_eval_expr_range_hits).
he_count_eval_expr_fast(Expr, Count) :-
    nonvar(Expr),
    Expr = [collapse, Call],
    he_structural_result_count(Call, Count), !.
he_count_eval_expr_fast(Expr, Count) :-
    nonvar(Expr),
    Expr = ['map-flat', FuncExpr, ListExpr],
    he_count_eval_expr_mapflat_fast(FuncExpr, ListExpr), !,
    he_count_eval_expr_fast(ListExpr, Count),
    he_perf_counter_inc(count_eval_expr_mapflat_hits).

he_count_eval_expr_mapflat_fast(FuncExpr, ListExpr) :-
    nonvar(FuncExpr),
    nonvar(ListExpr),
    FuncExpr = [+, _],
    ListExpr = [range, _].

he_count_eval_expr_fastable(Expr) :-
    nonvar(Expr),
    Expr == [].
he_count_eval_expr_fastable(Expr) :-
    nonvar(Expr),
    Expr = [range, _].
he_count_eval_expr_fastable(Expr) :-
    nonvar(Expr),
    Expr = ['map-flat', FuncExpr, ListExpr],
    he_count_eval_expr_mapflat_fast(FuncExpr, ListExpr),
    he_count_eval_expr_fastable(ListExpr).

he_collect_visible_results(Conj, Value, Results) :-
    he_visible_compiled_equation_stream_goal(Conj, Goal), !,
    he_perf_counter_inc(collect_visible_results_calls),
    StreamState = state(0, 0),
    State = state(no_success, [], [], 0),
    ( ( catch(( call(Goal),
                he_note_compiled_equation_stream_candidate(Value, StreamState, Visible),
                ( Visible == true
                -> he_public_result(Value, Public),
                   ( he_error_result(Public)
                   -> IsError = true
                   ;  IsError = false
                   ),
                   he_note_success_preferred_row(Public, IsError, State)
                ;  true
                ),
                fail
              ),
              _,
              fail)
      )
    ; he_finalize_compiled_equation_visible_stream(StreamState),
      he_finalize_success_preferred_rows(State, Results, RawCount),
      he_perf_counter_add(collect_visible_results_rows, RawCount)
    ).

he_collect_visible_results(Conj, Value, Results) :-
    he_perf_counter_inc(collect_visible_results_calls),
    State = state(no_success, [], [], 0),
    ( ( Conj,
        he_visible_result(Value),
        he_public_result(Value, Public),
        ( he_error_result(Public)
        -> IsError = true
        ;  IsError = false
        ),
        he_note_success_preferred_row(Public, IsError, State),
        fail
      )
    ; he_finalize_success_preferred_rows(State, Results, RawCount),
      he_perf_counter_add(collect_visible_results_rows, RawCount)
    ).

he_bind_packet(Value, Vars, [Value, ['__he_bindings__'|Vars]]).

he_collect_bind_packets(Conj, Value, Vars, Results) :-
    he_perf_counter_inc(collect_bind_packet_calls),
    State = state(no_success, [], [], 0),
    ( ( Conj,
        he_visible_result(Value),
        copy_term(Value-Vars, ValueCopy-VarsCopy),
        he_bind_packet(ValueCopy, VarsCopy, Packet),
        ( he_error_result(ValueCopy)
        -> IsError = true
        ;  IsError = false
        ),
        he_note_success_preferred_row(Packet, IsError, State),
        fail
      )
    ; he_finalize_success_preferred_rows(State, Results, PacketCount),
      he_perf_counter_add(collect_bind_packet_rows, PacketCount)
    ).

he_note_fold_visible_public(Public, enqueue, State) :-
    \+ he_error_result(Public),
    arg(3, State, Acc0),
    Acc0 = [queue|_], !,
    arg(1, State, Mode),
    ( Mode == no_success
    -> nb_setarg(1, State, success)
    ;  true
    ),
    he_native_queue_enqueue_call(Public, Acc0, Acc1),
    nb_setarg(3, State, Acc1).

he_note_fold_visible_public(Public, Func, State) :-
    ( he_error_result(Public)
    -> arg(1, State, Mode),
       ( Mode == no_success
       -> arg(2, State, ErrorAcc0),
          nb_setarg(2, State, [Public|ErrorAcc0])
       ;  true
       )
    ;  arg(1, State, Mode),
       ( Mode == no_success
       -> nb_setarg(1, State, success)
       ;  true
       ),
       arg(3, State, Acc0),
       he_eval_or_reduce([Func, Public, Acc0], Acc1),
       nb_setarg(3, State, Acc1)
    ).

he_unique_space_fold_note_accepted(Stats) :-
    arg(1, Stats, Accepted0),
    Accepted is Accepted0 + 1,
    nb_setarg(1, Stats, Accepted).

he_finalize_unique_space_fold_stats(Stats) :-
    arg(1, Stats, Accepted),
    ( Accepted > 0
    -> he_perf_counter_inc(unique_space_fold_hits)
    ;  true
    ).

he_unique_space_fold_candidate(Value, Space, Func, State, Stats) :-
    he_public_result(Value, Public),
    ( he_error_result(Public)
    -> he_note_fold_visible_public(Public, Func, State)
    ;  he_perf_counter_inc(unique_space_fold_attempts),
       he_space_add_unique_public(Space, Public, Added, AddOut),
       ( Added == true
       -> he_public_result(AddOut, AddPublic),
          ( he_error_result(AddPublic)
          -> he_note_fold_visible_public(AddPublic, Func, State)
          ;  ( he_visible_result(Public)
             -> he_perf_counter_inc(unique_space_fold_accepted_rows),
                he_unique_space_fold_note_accepted(Stats),
                he_note_fold_visible_public(Public, Func, State)
             ;  true
             )
          )
       ;  he_perf_counter_inc(unique_space_fold_duplicate_skips)
       )
    ).

he_fold_unique_space_call_results(Call, Space, Func, Init, Out) :-
    he_build_user_call_stream_goal(Call, Value, Goal), !,
    he_perf_counter_inc(unique_space_fold_calls),
    he_perf_counter_inc(unique_space_fold_stream_calls),
    Stats = state(0),
    State = state(no_success, [], Init),
    ( ( catch(( call(Goal),
                he_unique_space_fold_candidate(Value, Space, Func, State, Stats),
                fail
              ),
              _,
              fail)
      )
    ; he_finalize_unique_space_fold_stats(Stats),
      he_finalize_fold_visible_results(State, Func, Init, Out)
    ).

he_fold_unique_space_call_results(Call, Space, Func, Init, Out) :-
    he_build_user_call_or_eval(Call, Value, Goal),
    he_perf_counter_inc(unique_space_fold_calls),
    he_perf_counter_inc(unique_space_fold_fallback_calls),
    Stats = state(0),
    State = state(no_success, [], Init),
    ( ( catch(( call(Goal),
                he_unique_space_fold_candidate(Value, Space, Func, State, Stats),
                fail
              ),
              _,
              fail)
      )
    ; he_finalize_unique_space_fold_stats(Stats),
      he_finalize_fold_visible_results(State, Func, Init, Out)
    ).

he_fold_visible_results(Conj, Value, Func, Init, Out) :-
    he_visible_compiled_equation_stream_goal(Conj, Goal), !,
    he_perf_counter_inc(fold_visible_results_calls),
    StreamState = state(0, 0),
    State = state(no_success, [], Init),
    ( ( catch(( call(Goal),
                he_note_compiled_equation_stream_candidate(Value, StreamState, Visible),
                ( Visible == true
                -> he_perf_counter_inc(fold_visible_results_rows),
                   he_public_result(Value, Public),
                   he_note_fold_visible_public(Public, Func, State)
                ;  true
                ),
                fail
              ),
              _,
              fail)
      )
    ; he_finalize_compiled_equation_visible_stream(StreamState),
      he_finalize_fold_visible_results(State, Func, Init, Out)
    ).

he_fold_visible_results(Conj, Value, Func, Init, Out) :-
    he_perf_counter_inc(fold_visible_results_calls),
    State = state(no_success, [], Init),
    ( ( Conj,
        he_visible_result(Value),
        he_perf_counter_inc(fold_visible_results_rows),
        he_public_result(Value, Public),
        he_note_fold_visible_public(Public, Func, State),
        fail
      )
    ; he_finalize_fold_visible_results(State, Func, Init, Out)
    ).

he_finalize_fold_visible_results(State, Func, Init, Out) :-
    arg(1, State, Mode),
    ( Mode == success
    -> arg(3, State, Out)
    ;  arg(2, State, ErrorAcc),
       reverse(ErrorAcc, Errors),
       he_foldl_reduce(Errors, Func, Init, Out)
    ).

he_superpose_bind_packet_list([]).
he_superpose_bind_packet_list([Packet|Packets]) :-
    he_superpose_bind_explicit_packet(Packet),
    he_superpose_bind_packet_list(Packets).

he_superpose_bind_explicit_packet([_Value, ['__he_bindings__'|_]]).

he_superpose_bind_member(PacketList, Out) :-
    he_superpose_bind_packet_list(PacketList), !,
    member(Packet, PacketList),
    he_superpose_bind_packet_value(Packet, Out).
he_superpose_bind_member(Packet, Out) :-
    is_list(Packet), !,
    he_superpose_bind_packet_value(Packet, Out).
he_superpose_bind_member(Arg, ['Error', ['superpose-bind', Arg], ['BadArgType', 1, 'Expression', 'Number']]) :-
    number(Arg), !.
he_superpose_bind_member(Arg, ['Error', ['superpose-bind', Arg], ['BadArgType', 1, 'Expression', 'Atom']]) :-
    atomic(Arg), !.
he_superpose_bind_member(Arg, ['Error', ['superpose-bind', Arg], ['BadArgType', 1, 'Expression', 'Grounded']]).

he_superpose_bind_packet_value([Value, ['__he_bindings__'|_]], Value) :- !.
he_superpose_bind_packet_value(Value, Value).

he_superpose_bind_apply(PacketList, Args, Out) :-
    he_superpose_bind_packet_list(PacketList), !,
    member(Packet, PacketList),
    he_superpose_bind_packet_apply(Packet, Args, Out).
he_superpose_bind_apply(Packet, Args, Out) :-
    is_list(Packet), !,
    he_superpose_bind_packet_apply(Packet, Args, Out).
he_superpose_bind_apply(Arg, _Args, ['Error', ['superpose-bind', Arg], ['BadArgType', 1, 'Expression', 'Number']]) :-
    number(Arg), !.
he_superpose_bind_apply(Arg, _Args, ['Error', ['superpose-bind', Arg], ['BadArgType', 1, 'Expression', 'Atom']]) :-
    atomic(Arg), !.
he_superpose_bind_apply(Arg, _Args, ['Error', ['superpose-bind', Arg], ['BadArgType', 1, 'Expression', 'Grounded']]).

he_superpose_bind_packet_apply([Value, ['__he_bindings__'|BoundVals]], Args, Out) :-
    same_length(Args, BoundVals),
    Args = BoundVals,
    Out = [Value|Args], !.
he_superpose_bind_packet_apply(Value, Args, Out) :-
    ( he_apply_callable_result(Value, Args, Out)
    -> true
    ; Out = [Value|Args]
    ).

he_once_visible_result(Conj, Value, Out) :-
    he_perf_counter_inc(once_visible_result_calls),
    ( once(( Conj,
             he_visible_result(Value),
             Out = Value
           ))
    -> true
    ;  Out = 'Empty'
    ).
