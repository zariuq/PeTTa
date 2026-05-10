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

he_fold_visible_results(Conj, Value, Func, Init, Out) :-
    he_perf_counter_inc(fold_visible_results_calls),
    State = state(no_success, [], Init),
    ( ( Conj,
        he_visible_result(Value),
        he_perf_counter_inc(fold_visible_results_rows),
        he_public_result(Value, Public),
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
        ),
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
