%Since both normal add-attom call and function additions needs to add the S-expression:
:- discontiguous match/4.
:- discontiguous 'add-atom'/3.
:- discontiguous 'remove-atom'/3.

add_sexp(Space, Term) :- \+ is_list(Term), !,
                         TermWithSpace =.. [Space, Term],
                         assertz(TermWithSpace).
add_sexp(Space, [Rel|Args]) :- Term =.. [Space, Rel | Args],
                               assertz(Term).

%Same but for removal:
remove_sexp(Space, Term) :- \+ is_list(Term), !,
                            TermWithSpace =.. [Space, Term],
                            once(retract(TermWithSpace)).
remove_sexp(Space, [Rel|Args]) :- Term =.. [Space, Rel | Args],
                                  once(retract(Term)).

'add-atom'(Space0, Term, Out) :-
    he_bridge_space_ref(Space0, Space),
    Space \== Space0, !,
    'add-atom'(Space, Term, Out).

'remove-atom'(Space0, Term, Out) :-
    he_bridge_space_ref(Space0, Space),
    Space \== Space0, !,
    'remove-atom'(Space, Term, Out).

%Add a function atom to &self:
'add-atom'('&self', Term, Out) :- Term = [=,[FAtom|W],_], atom(FAtom), !,
                                 add_sexp('&self', Term),
                                 he_note_space_fact_added('&self', Term),
                                 register_fun(FAtom),
                                 length(W, N),
                                 Arity is N + 1,
                                 ( arity(FAtom, Arity) -> true ; assertz(arity(FAtom,Arity)) ),
                                 he_clause_functor(FAtom, ClauseFunctor),
                                 once(translate_clause(Term, Clause, true, ClauseFunctor)),
                                 assertz(Clause, Ref),
	                                 assertz(translated_from(Ref, Term)),
	                                 invalidate_specializations(FAtom),
	                                 maybe_print_compiled_clause("added function", Term, Clause),
	                                 he_bridge_result([], true, Out).

%Add an atom to the space:
'add-atom'(Space, Term, Out) :- add_sexp(Space, Term),
                                he_note_space_fact_added(Space, Term),
                                he_bridge_result([], true, Out).

%%Remove a function atom:
'remove-atom'('&self', Term, Removed) :- Term = [=,[F|Args],Body], atom(F), !,
                                         remove_sexp('&self', Term),
                                         he_note_space_fact_removed('&self', Term),
                                         catch(nb_getval(F, Prev), _, Prev = []),
                                         (   select(fun_meta(Args, Body), Prev, Rest)
                                             -> ( Rest == [] -> nb_delete(F)
                                                              ; nb_setval(F, Rest) ) ; true ),
                                         findall(Ref, translated_from(Ref, Term), Refs),
                                         forall(member(Ref, Refs), erase(Ref)),
                                         retractall(translated_from(_, Term)),
                                         invalidate_specializations(F),
                                         he_clause_functor(F, ClauseFunctor),
                                         ( \+ ( current_predicate(ClauseFunctor/A), functor(H2, ClauseFunctor, A), clause(H2, _, _) )
                                           -> retractall(fun(F)) ; true ),
                                         ( Refs = [] -> Removed = false ; Removed = true ).

%Remove all same atoms:
'remove-atom'(Space, Term, true) :- remove_sexp(Space, Term),
                                    he_note_space_fact_removed(Space, Term).

match('&self', Pattern, OutPattern, Result) :-
    he_profile_enabled,
    he_fast_plain_self_matchable(Pattern), !,
    he_direct_space_match('&self', Pattern, OutPattern, Result).

match(Space0, Pattern, OutPattern, Result) :-
    he_bridge_space_ref(Space0, Space),
    Space \== Space0, !,
    match(Space, Pattern, OutPattern, Result).

match(Space, Pattern, OutPattern, Result) :-
    he_bridge_match_override(Space, Pattern, OutPattern, Result).
match(_, Pattern, _, _) :-
    he_bridge_match_blocked(Pattern), !,
    fail.

%Match for conjunctive pattern
match(_, LComma, OutPattern, Result) :- LComma == [','], !,
                                        Result = OutPattern.
match(Space, [Comma|[Head|Tail]], OutPattern, Result) :- Comma == ',', !,
                                                         append([Space], Head, List),
                                                         Term =.. List,
                                                         catch(Term, _, fail),
                                                         \+ cyclic_term(OutPattern),
                                                         match(Space, [','|Tail], OutPattern, Result).

match(Space, Pattern, OutPattern, Result) :-
    he_direct_space_match(Space, Pattern, OutPattern, Result).

he_direct_space_match(Space, PatternVar, OutPattern, Result) :-
    var(PatternVar), !,
    'get-atoms'(Space, PatternVar),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.
he_direct_space_match(Space, Pattern, OutPattern, Result) :-
    \+ is_list(Pattern), !,
    Term =.. [Space, Pattern],
    catch(Term, _, fail),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.
he_direct_space_match(Space, [Rel|PatArgs], OutPattern, Result) :-
    Term =.. [Space, Rel | PatArgs],
    catch(Term, _, fail),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

%Get all atoms in space, irregard of arity:
'get-atoms'(Space0, Pattern) :-
                               he_bridge_space_ref(Space0, Space),
                               Space \== Space0, !,
                               'get-atoms'(Space, Pattern).
'get-atoms'(Space, Pattern) :- current_predicate(Space/Arity),
                               functor(Head, Space, Arity),
                               clause(Head, true),
                               Head =.. [Space | Pattern].
