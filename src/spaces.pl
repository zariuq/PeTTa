%Arity expander for JIT-indexing-efficient representation of space entries:
ensure_dynamic_arity(Space,Arity) :- ( current_predicate(Space/Arity)
                                       -> true ; dynamic(Space/Arity) ).

%Since both normal add-attom call and function additions needs to add the S-expression:
add_sexp(Space, [Rel|Args]) :- length(Args, N), Arity is N + 2,
                               ensure_dynamic_arity(Space, Arity),
                               Term =.. [Space, Rel | Args],
                               assertz(Term).

% Convert user spaces to tagged subspaces in &self
'add-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|Rest]),
    Rest \== [], !,
    atom_chars(SpaceName, Rest),
    'add-atom'('&self', [subspace, SpaceName, Atom], Result).

%Add a function atom:
'add-atom'(Space, Term, true) :- Term = [=,[FAtom|W],_], !,
                                 add_sexp(Space, Term),
                                 register_fun(FAtom),
                                 length(W, N),
                                 Arity is N + 1,
                                 assertz(arity(FAtom,Arity)),
                                 working_directory(CWD, CWD),
                                 translate_clause(Term, CWD, Clause),
                                 assertz(Clause),
                                 ( silent(true) -> true ; format("\e[33m--> added clause -->~n\e[32m", []),
                                                          Clause = (CHead :- CBody),
                                                          ( CBody == true -> Show = CHead; Show = (CHead :- CBody) ),
                                                          portray_clause(current_output, Show),
                                                          format("\e[33m^^^^^^^^^^^^^^^^^^^^^~n\e[0m") ).

%Add an atom to the space:
'add-atom'(Space, Term, true) :- add_sexp(Space, Term).

%%Remove a function atom:
'remove-atom'('&self', Term, Removed) :- Term = [=,[F|Ins],_], !,
                                         retractall(Term),
                                         working_directory(CWD, CWD),
                                         translate_clause(Term, CWD, Cl),
                                         ( retract(Cl) -> length(Ins, K),
                                                          unregister_fun(F/K),
                                                          Removed=true
                                                        ; Removed=false ).

%Remove all same atoms:
'remove-atom'(Space, [Rel|Args], true) :- length(Args, N), Arity is N + 2,
                                          ensure_dynamic_arity(Space, Arity),
                                          Term =.. [Space, Rel | Args],
                                          retractall(Term).

% Elegant fix: Convert user spaces to tagged subspaces in &self
match(Space, Pattern, OutPattern, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|Rest]),
    Rest \== [], !,
    atom_chars(SpaceName, Rest),
    % Match the wrapped pattern and extract the result
    match('&self', [subspace, SpaceName, Pattern], [subspace, SpaceName, OutPattern], Result).

%Match for conjunctive pattern
match(_, LComma, OutPattern, Result) :- LComma == [','], !,
                                        Result = OutPattern.
match(Space, [Comma|[Head|Tail]], OutPattern, Result) :- Comma == ',', !,
                                                         append([Space], Head, List),
                                                         Term =.. List,
                                                         catch(Term, _, fail),
                                                         \+ cyclic_term(OutPattern),
                                                         match(Space, [','|Tail], OutPattern, Result).

% When the pattern list itself is a variable -> enumerate all atoms
match(Space, PatternVar, OutPattern, Result) :- var(PatternVar), !,
                                                'get-atoms'(Space, PatternVar),
                                                \+ cyclic_term(OutPattern),
                                                Result = OutPattern.

%Match for pattern:
match(Space, [Rel|PatArgs], OutPattern, Result) :- Term =.. [Space, Rel | PatArgs],
                                                   catch(Term, _, fail),
                                                   \+ cyclic_term(OutPattern),
                                                   Result = OutPattern.

%Get all atoms in space, irregard of arity:
'get-atoms'(Space, Pattern) :- current_predicate(Space/Arity),
                               functor(Head, Space, Arity),
                               clause(Head, true),
                               Head =.. [Space | Pattern].
