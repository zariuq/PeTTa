:- dynamic arity/2.
:- dynamic he_import_loaded/0.
:- dynamic he_profile_enabled/0.
:- dynamic he_runtime_loaded/0.
:- dynamic he_state_loaded/0.
:- dynamic he_types_loaded/0.
:- dynamic metta_profile/1.
:- dynamic 'bind!'/3.
:- dynamic 'change-state!'/3.
:- dynamic 'get-metatype'/2.
:- dynamic 'get-state'/2.
:- dynamic 'get-type'/2.
:- dynamic 'is-expr'/2.
:- dynamic 'is-space'/2.
:- dynamic 'is-var'/2.
:- dynamic 'new-state'/2.

:- multifile 'bind!'/3.
:- multifile 'change-state!'/3.
:- multifile 'get-metatype'/2.
:- multifile 'get-state'/2.
:- multifile 'get-type'/2.
:- multifile 'is-expr'/2.
:- multifile 'is-space'/2.
:- multifile 'is-var'/2.
:- multifile 'new-state'/2.

:- discontiguous 'bind!'/3.
:- discontiguous 'change-state!'/3.
:- discontiguous 'get-metatype'/2.
:- discontiguous 'get-state'/2.
:- discontiguous 'get-type'/2.
:- discontiguous 'is-expr'/2.
:- discontiguous 'is-space'/2.
:- discontiguous 'is-var'/2.
:- discontiguous 'new-state'/2.

:- multifile he_bridge_clause_constrains_args/1.
:- multifile he_bridge_compare/4.
:- multifile he_bridge_eval_data_term/3.
:- multifile he_bridge_eval_goal/3.
:- multifile he_bridge_import/3.
:- multifile he_bridge_lower_clause_body/3.
:- multifile he_bridge_match_blocked/1.
:- multifile he_bridge_match_override/4.
:- multifile he_bridge_partial_or_data/3.
:- multifile he_bridge_reduce/3.
:- multifile he_bridge_result/3.
:- multifile he_bridge_run_runnable/2.
:- multifile he_bridge_space_ref/2.
:- multifile he_clause_functor/2.
:- multifile he_invalidate_all_function_typechain_cache/0.
:- multifile he_invalidate_function_typechain_cache/1.
:- multifile he_known_fun_dispatch/9.
:- multifile he_note_space_fact_added/2.
:- multifile he_note_space_fact_removed/2.
:- multifile he_space_fact_added_hook/2.
:- multifile he_space_fact_removed_hook/2.
:- multifile he_post_builtin_dispatch/5.
:- multifile he_pre_builtin_dispatch/5.
:- multifile he_unknown_or_callable_dispatch/5.

:- discontiguous he_bridge_clause_constrains_args/1.
:- discontiguous he_bridge_compare/4.
:- discontiguous he_bridge_eval_data_term/3.
:- discontiguous he_bridge_eval_goal/3.
:- discontiguous he_bridge_import/3.
:- discontiguous he_bridge_lower_clause_body/3.
:- discontiguous he_bridge_match_blocked/1.
:- discontiguous he_bridge_match_override/4.
:- discontiguous he_bridge_partial_or_data/3.
:- discontiguous he_bridge_reduce/3.
:- discontiguous he_bridge_result/3.
:- discontiguous he_bridge_run_runnable/2.
:- discontiguous he_bridge_space_ref/2.
:- discontiguous he_clause_functor/2.
:- discontiguous he_invalidate_all_function_typechain_cache/0.
:- discontiguous he_invalidate_function_typechain_cache/1.
:- discontiguous he_known_fun_dispatch/9.
:- discontiguous he_note_space_fact_added/2.
:- discontiguous he_note_space_fact_removed/2.
:- discontiguous he_space_fact_added_hook/2.
:- discontiguous he_space_fact_removed_hook/2.
:- discontiguous he_post_builtin_dispatch/5.
:- discontiguous he_pre_builtin_dispatch/5.
:- discontiguous he_unknown_or_callable_dispatch/5.

:- prolog_load_context(directory, HeDir),
   asserta(he_boot_dir(HeDir)).
:- dynamic he_boot_dir/1.

metta_profile_from_args(Args, he) :-
    memberchk('--he', Args), !.
metta_profile_from_args(_, petta).

set_metta_profile_from_args(Args) :-
    metta_profile_from_args(Args, Profile),
    set_metta_profile(Profile).

set_metta_profile(Profile) :-
    retractall(metta_profile(_)),
    retractall(he_profile_enabled),
    assertz(metta_profile(Profile)),
    ( Profile == he
    -> assertz(he_profile_enabled),
       ensure_he_runtime_loaded,
       ( current_predicate(install_profile/1),
         current_predicate(register_fun/1)
       -> install_profile(he)
       ; true )
    ; true ).

he_space_ref_atom(Term) :-
    atom(Term),
    atom_prefix(Term, '&').

mark_he_runtime_loaded :-
    ( he_runtime_loaded -> true ; assertz(he_runtime_loaded) ).

ensure_he_runtime_loaded :-
    he_runtime_loaded, !.
ensure_he_runtime_loaded :-
    he_boot_dir(Dir),
    directory_file_path(Dir, he_bridge, Bridge),
    ensure_loaded(Bridge),
    mark_he_runtime_loaded.

ensure_he_import_loaded :-
    he_import_loaded, !.
ensure_he_import_loaded :-
    he_boot_dir(Dir),
    directory_file_path(Dir, he_import, Import),
    ensure_loaded(Import),
    assertz(he_import_loaded).

ensure_he_types_loaded :-
    he_types_loaded, !.
ensure_he_types_loaded :-
    he_boot_dir(Dir),
    directory_file_path(Dir, he_types, Types),
    ensure_loaded(Types),
    assertz(he_types_loaded).

ensure_he_state_loaded :-
    he_state_loaded, !.
ensure_he_state_loaded :-
    he_boot_dir(Dir),
    directory_file_path(Dir, he_state, State),
    ensure_loaded(State),
    assertz(he_state_loaded).

register_he_compat_helper(Name, Arity) :-
    register_fun(Name),
    ( arity(Name, Arity) -> true ; assertz(arity(Name, Arity)) ).

he_note_space_fact_added(Space, Term) :-
    forall(he_space_fact_added_hook(Space, Term), true).
he_note_space_fact_removed(Space, Term) :-
    forall(he_space_fact_removed_hook(Space, Term), true).
he_space_fact_added_hook(_, _) :-
    fail.
he_space_fact_removed_hook(_, _) :-
    fail.
he_invalidate_function_typechain_cache(_) :-
    \+ he_types_loaded, !.
he_invalidate_all_function_typechain_cache :-
    \+ he_types_loaded, !.

'bind!'(A, B, Out) :-
    \+ he_state_loaded,
    ensure_he_state_loaded, !,
    'bind!'(A, B, Out).

'new-state'(Value, State) :-
    \+ he_state_loaded,
    ensure_he_state_loaded, !,
    'new-state'(Value, State).

'change-state!'(Target, Value, Out) :-
    \+ he_state_loaded,
    ensure_he_state_loaded, !,
    'change-state!'(Target, Value, Out).

'get-state'(Target, Value) :-
    \+ he_state_loaded,
    ensure_he_state_loaded, !,
    'get-state'(Target, Value).

'get-type'(X, T) :-
    \+ he_types_loaded,
    ensure_he_types_loaded, !,
    'get-type'(X, T).

'get-metatype'(X, T) :-
    \+ he_types_loaded,
    ensure_he_types_loaded, !,
    'get-metatype'(X, T).

'is-var'(X, R) :-
    \+ he_types_loaded,
    ensure_he_types_loaded, !,
    'is-var'(X, R).

'is-expr'(X, R) :-
    \+ he_types_loaded,
    ensure_he_types_loaded, !,
    'is-expr'(X, R).

'is-space'(X, R) :-
    \+ he_types_loaded,
    ensure_he_types_loaded, !,
    'is-space'(X, R).

he_bridge_import(Space, File, true) :-
    ensure_he_import_loaded,
    catch(importer_helper(Space, File), _, fail), !.

he_bridge_lower_clause_body(_, _, _) :- fail.

he_bridge_compare(_, _, _, _) :- fail.
he_pre_builtin_dispatch(_, _, _, _, _) :- fail.
he_bridge_clause_constrains_args(ConstrainArgs) :-
    \+ he_profile_enabled,
    ConstrainArgs.
he_bridge_reduce(F, Args, Out) :-
    \+ he_profile_enabled, !,
    append(Args, [Out], CallArgs),
    Goal =.. [F|CallArgs],
    catch(call(Goal), _, fail).

he_bridge_eval_goal(Arg, Out, eval(Arg, Out)) :-
    \+ he_profile_enabled, !.
he_post_builtin_dispatch(_, _, _, _, _) :- fail.
he_known_fun_dispatch(Fun, AllAVs, Out, Inner, T, GsH, IsPartial, Bound, Goals) :-
    \+ he_profile_enabled, !,
    findall(TypeChain,
            catch(match('&self', [':', Fun, TypeChain], TypeChain, TypeChain), _, fail),
            TypeChains),
    ( TypeChains \= []
    -> maplist({Fun,T,GsH,IsPartial,Bound,Out}/[TypeChain,BranchGoal]>>(
           typed_functioncall_branch(Fun, TypeChain, T, GsH, IsPartial, Bound, Out, BranchGoal)),
           TypeChains,
           Branches),
       disj_list(Branches, Disj),
       Goals = [Disj]
    ; build_call_or_partial(Fun, AllAVs, Out, Inner, [], Goals)
    ).
he_unknown_or_callable_dispatch(_, _, _, _, _) :- fail.
he_bridge_partial_or_data(Fun, AVs, partial(Fun, AVs)) :-
    \+ he_profile_enabled, !.
he_bridge_eval_data_term(_, _, _) :- fail.
he_bridge_match_override(_, _, _, _) :- fail.
he_bridge_match_blocked(_) :- fail.

he_bridge_space_ref(Space, Space) :-
    \+ he_profile_enabled, !.

he_bridge_result(_HeOut, DefaultOut, DefaultOut) :-
    \+ he_profile_enabled, !.

he_clause_functor(Fun, Fun) :-
    \+ he_profile_enabled, !.

he_bridge_run_runnable(Goals, _Result) :-
    \+ he_profile_enabled, !,
    call_goals(Goals).
