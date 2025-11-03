% Final elegant fix: Transform space names to valid Prolog predicates
% &kb becomes space_kb, &self becomes space_self, etc.

% Helper to convert space names to valid Prolog predicates
space_to_predicate(Space, Predicate) :-
    atom(Space),
    atom_chars(Space, ['&'|Rest]),
    atom_chars(CleanName, Rest),
    atom_concat('space_', CleanName, Predicate), !.
space_to_predicate(Space, Space).  % Non-& names pass through

% Override add_sexp to use transformed names
add_sexp_fixed(Space, [Rel|Args]) :-
    space_to_predicate(Space, PredSpace),
    length(Args, N),
    Arity is N + 2,
    ensure_dynamic_arity(PredSpace, Arity),
    Term =.. [PredSpace, Rel | Args],
    assertz(Term).

% Override match to use transformed names
match_fixed(Space, [Rel|PatArgs], OutPattern, Result) :-
    space_to_predicate(Space, PredSpace),
    Term =.. [PredSpace, Rel | PatArgs],
    Term,
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

% This way:
% - &kb becomes the Prolog predicate space_kb
% - &self becomes space_self
% - Everything works with valid Prolog syntax!