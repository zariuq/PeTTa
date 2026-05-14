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
    Call = [Fun|Args],
    he_bound_single_equation_body(Fun, Args, Body),
    he_effect_only_match_count_body(Body, PrefixExpr, SpaceExpr, Pattern), !,
    he_perf_counter_inc(count_visible_results_calls),
    he_perf_counter_inc(count_visible_results_match_fast_hits),
    once(he_effect_only_expr(PrefixExpr)),
    he_eval_runtime_arg(SpaceExpr, Space),
    he_space_pattern_result_count(Space, Pattern, Count),
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
