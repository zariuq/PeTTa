:- ensure_loaded(['he_boot',
                  'he_profile',
                  'he_import',
                  'he_spaces',
                  'he_types',
                  'he_assertions',
                  'he_natives',
                  'he_state',
                  'he_call',
                  'he_translator',
                  'he_match',
                  'he_docs']).

:- ( he_import_loaded -> true ; assertz(he_import_loaded) ).
:- ( he_types_loaded -> true ; assertz(he_types_loaded) ).
:- ( he_state_loaded -> true ; assertz(he_state_loaded) ).
:- mark_he_runtime_loaded.

:- multifile he_bridge_clause_constrains_args/1.
:- multifile he_bridge_compare/4.
:- multifile he_bridge_eval_data_term/3.
:- multifile he_bridge_eval_goal/3.
:- multifile he_bridge_lower_clause_body/3.
:- multifile he_bridge_match_blocked/1.
:- multifile he_bridge_match_override/4.
:- multifile he_bridge_partial_or_data/3.
:- multifile he_bridge_reduce/3.
:- multifile he_bridge_result/3.
:- multifile he_bridge_run_runnable/2.
:- multifile he_bridge_space_ref/2.
:- multifile he_known_fun_dispatch/9.
:- multifile he_post_builtin_dispatch/5.
:- multifile he_pre_builtin_dispatch/5.
:- multifile he_unknown_or_callable_dispatch/5.

he_pre_builtin_dispatch(HV, T, GsH, Out, Goals) :-
    he_profile_enabled,
    he_translate_special(HV, T, GsH, Out, Goals).

he_bridge_compare(eq, A, B, R) :-
    he_profile_eq(A, B, R).
he_bridge_compare(ne, A, B, R) :-
    he_profile_ne(A, B, R).

he_bridge_clause_constrains_args(ConstrainArgs) :-
    he_clause_constrains_args(ConstrainArgs).

he_bridge_lower_clause_body(Expr, Goals, Out) :-
    he_profile_enabled,
    he_lower_clause_body(Expr, Goals, Out).

he_bridge_reduce(F, Args, Out) :-
    he_profile_enabled,
    fun(F), !,
    he_reduce_known_fun(F, Args, Out).
he_bridge_reduce(F, Args, Out) :-
    length(Args, N),
    Arity is N + 1,
    current_predicate(F/Arity),
    \+ (current_op(_, _, F), Arity =< 2), !,
    he_reduce_known_fun(F, Args, Out).
he_bridge_reduce(F, Args, Out) :-
    he_reduce_missing_fun(F, Args, Out).

he_bridge_eval_goal(Arg, Out, Goal) :-
    he_eval_goal(Arg, Out, Goal).

he_post_builtin_dispatch(HV, T, GsH, Out, Goals) :-
    he_native_helper_dispatch(HV, T, GsH, Out, Goals).
he_post_builtin_dispatch(HV, T, GsH, Out, Goals) :-
    he_typed_dispatch(HV, T, GsH, Out, Goals).

he_known_fun_dispatch(Fun, AllAVs, Out, Inner, T, GsH, IsPartial, Bound, Goals) :-
    he_smart_known_fun(Fun, AllAVs, Out, Inner, T, GsH, IsPartial, Bound, Goals).

he_unknown_or_callable_dispatch(HV, AVs, Out, Inner, Goals) :-
    he_unknown_head_dispatch(HV, AVs, Out, Inner, Goals).
he_unknown_or_callable_dispatch(HV, AVs, Out, Inner, Goals) :-
    he_callable_head_dispatch(HV, AVs, Out, Inner, Goals).

he_bridge_partial_or_data(Fun, AVs, Out) :-
    he_partial_or_data(Fun, AVs, Out).

he_bridge_eval_data_term(List, Goals, Val) :-
    he_eval_data_term(List, Goals, Val).

he_bridge_space_ref(Space0, Space) :-
    he_resolve_space_ref(Space0, Space).

he_bridge_result(HeOut, DefaultOut, Out) :-
    he_profile_result(HeOut, DefaultOut, Out).

he_bridge_match_override(_Space, Pattern, OutPattern, Result) :-
    he_match_runtime_counter(Pattern, OutPattern, Result).
he_bridge_match_override(Space, Pattern, OutPattern, Result) :-
    he_match_state_semantic(Space, Pattern, OutPattern, Result).
he_bridge_match_override(Space, [=, Call, BodyPattern], OutPattern, Result) :-
    he_match_equation(Space, Call, BodyPattern, OutPattern, Result).
he_bridge_match_override(Space, Pattern, OutPattern, Result) :-
    he_match_generic_list(Space, Pattern, OutPattern, Result).

he_bridge_match_blocked([=, Call, _]) :-
    he_blocks_generic_equation_match(Call), !.
he_bridge_match_blocked(Pattern) :-
    he_blocks_generic_list_match(Pattern), !.

he_bridge_run_runnable(Goals, Result) :-
    catch(call_goals(Goals),
          he_return(Returned),
          Result = [['Error', [return, Returned], 'NoReturn']]).
