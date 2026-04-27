he_match_runtime_counter(Pattern, OutPattern, Result) :-
    nonvar(Pattern),
    Pattern = [Head, _, Value],
    nonvar(Head),
    Head == 'runtime-counter', !,
    Value = 0,
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

he_fast_plain_self_matchable(Pattern) :-
    nonvar(Pattern),
    he_fast_plain_self_root(Pattern).

he_fast_plain_self_root([Head, _, _]) :-
    nonvar(Head),
    Head == 'runtime-counter', !,
    fail.
he_fast_plain_self_root([=, Call, _]) :-
    is_list(Call),
    Call = [_|CallArgs],
    CallArgs \= [], !,
    fail.
he_fast_plain_self_root([Rel]) :- !,
    he_plain_non_state_atom(Rel).
he_fast_plain_self_root([Rel, A]) :- !,
    he_plain_non_state_atom(Rel),
    he_plain_fast_arg(A).
he_fast_plain_self_root([Rel, A, B]) :- !,
    he_plain_non_state_atom(Rel),
    he_plain_fast_arg(A),
    he_plain_fast_arg(B).
he_fast_plain_self_root([Rel, A, B, C]) :- !,
    he_plain_non_state_atom(Rel),
    he_plain_fast_arg(A),
    he_plain_fast_arg(B),
    he_plain_fast_arg(C).
he_fast_plain_self_root([Rel|Args]) :- !,
    he_plain_non_state_atom(Rel),
    he_plain_terms_without_state_ref(Args).
he_fast_plain_self_root(Term) :-
    he_plain_term_without_state_ref(Term).

he_plain_non_state_atom(Term) :-
    atom(Term),
    he_plain_atom_cache(Term), !.
he_plain_non_state_atom(Term) :-
    atom(Term),
    \+ he_space_ref_atom(Term).

he_plain_fast_arg(Term) :-
    var(Term), !.
he_plain_fast_arg(Term) :-
    atomic(Term), !,
    ( atom(Term)
    -> he_plain_non_state_atom(Term)
    ; true ).
he_plain_fast_arg(Term) :-
    he_plain_term_without_state_ref(Term).

he_plain_term_without_state_ref(Term) :-
    var(Term), !.
he_plain_term_without_state_ref(Term) :-
    atomic(Term), !,
    ( atom(Term)
    -> he_plain_non_state_atom(Term)
    ; true ).
he_plain_term_without_state_ref([A]) :- !,
    he_plain_fast_arg(A).
he_plain_term_without_state_ref([A, B]) :- !,
    he_plain_fast_arg(A),
    he_plain_fast_arg(B).
he_plain_term_without_state_ref([A, B, C]) :- !,
    he_plain_fast_arg(A),
    he_plain_fast_arg(B),
    he_plain_fast_arg(C).
he_plain_term_without_state_ref([A, B, C, D]) :- !,
    he_plain_fast_arg(A),
    he_plain_fast_arg(B),
    he_plain_fast_arg(C),
    he_plain_fast_arg(D).
he_plain_term_without_state_ref([Head|Args]) :- !,
    he_plain_fast_arg(Head),
    he_plain_terms_without_state_ref(Args).
he_plain_term_without_state_ref(Term) :-
    compound(Term),
    compound_name_arguments(Term, _, Args),
    he_plain_terms_without_state_ref(Args).

he_plain_terms_without_state_ref([]).
he_plain_terms_without_state_ref([Arg|Args]) :-
    he_plain_term_without_state_ref(Arg),
    he_plain_terms_without_state_ref(Args).

he_match_state_semantic(Space, Pattern, OutPattern, Result) :-
    he_match_requires_state_semantics(Pattern), !,
    he_match_semantic(Space, Pattern, OutPattern, Result).

he_match_equation(Space, Call, BodyPattern, OutPattern, Result) :-
    Space == '&self',
    Call = [Fun|CallArgs],
    atom(Fun),
    length(CallArgs, Arity),
    he_eq_fact(Fun, Arity, HeadArgs, StoredBody0), !,
    HeadArgs = CallArgs,
    ( ground(Call)
    -> he_eval_or_raw(StoredBody0, BodyPattern)
    ; BodyPattern = StoredBody0
    ),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.
he_match_equation(Space, Call, BodyPattern, OutPattern, Result) :-
    \+ ( Call = [Fun|_], atom(Fun) ),
    is_list(Call),
    Call = [_|CallArgs],
    CallArgs \= [],
    ( ground(Call) -> GroundCall = true ; GroundCall = false ),
    he_space_atom(Space, [=, StoredHead, StoredBody]),
    is_list(StoredHead),
    StoredHead = Call,
    ( GroundCall == true
    -> he_eval_or_raw(StoredBody, BodyPattern)
    ; BodyPattern = StoredBody
    ),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

he_blocks_generic_equation_match(Call) :-
    is_list(Call),
    Call = [_|CallArgs],
    CallArgs \= [].

he_match_generic_list(Space, Pattern, OutPattern, Result) :-
    is_list(Pattern),
    he_generic_list_pattern(Pattern),
    he_space_atom_list_form(Space, Stored),
    Pattern = Stored,
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

he_blocks_generic_list_match(Pattern) :-
    is_list(Pattern),
    he_generic_list_pattern(Pattern).

he_match_requires_state_semantics(Pattern) :-
    he_term_has_state(Pattern).

he_term_has_state(Term) :-
    var(Term), !,
    fail.
he_term_has_state(Term) :-
    atom(Term),
    he_space_ref_atom(Term),
    catch(nb_getval(Term, Bound), _, fail),
    he_state_handle(Bound, _), !.
he_term_has_state(Term) :-
    he_state_handle(Term, _), !.
he_term_has_state(Term) :-
    is_list(Term), !,
    he_term_has_state_list(Term).
he_term_has_state(Term) :-
    compound(Term),
    compound_name_arguments(Term, _, Args),
    he_term_has_state_list(Args).

he_term_has_state_list([Elem|_]) :-
    he_term_has_state(Elem), !.
he_term_has_state_list([_|Elems]) :-
    he_term_has_state_list(Elems).

he_space_atom(Space, Atom) :-
    current_predicate(Space/Arity),
    functor(Head, Space, Arity),
    clause(Head, true),
    Head =.. [Space|Args],
    ( Args = [Rel|Rest]
      -> ( Rest == [] -> Atom = Rel ; Atom = [Rel|Rest] )
      ; Atom = [] ).

he_space_atom_list_form(Space, Atom) :-
    current_predicate(Space/Arity),
    functor(Head, Space, Arity),
    clause(Head, true),
    Head =.. [Space|Atom].

he_eval_or_raw(Expr, Value) :-
    catch(eval(Expr, Value), _, fail).
he_eval_or_raw(Expr, Expr) :-
    \+ catch(once(eval(Expr, _)), _, fail).

he_match_semantic(Space, Pattern, OutPattern, Result) :-
    he_space_atom(Space, Stored),
    he_normalize_state_term(Pattern, PatternN),
    he_normalize_state_term(Stored, StoredN),
    PatternN = StoredN,
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

he_generic_list_pattern([Rel|_]) :- var(Rel), !.
he_generic_list_pattern([Rel|_]) :- \+ atom(Rel).
