%Since both normal add-attom call and function additions needs to add the S-expression.
%The atoms of &self also maintain the declarations the compiler reads (types.pl):
add_sexp(Space, TermIn) :-
    ( is_list(TermIn), TermIn = [Rel|Args] ->
        Term =.. [Space, Rel | Args],
        assertz(Term),
        ( Space == '&self' -> note_type_decl(TermIn) ; true )
    ;
        Term =.. [Space, '#primitive', TermIn],
        assertz(Term)
    ).

%Same but for removal:
remove_sexp(Space, TermIn) :-
    ( is_list(TermIn), TermIn = [Rel|Args] ->
        Term =.. [Space, Rel | Args],
        retractall(Term),
        ( Space == '&self' -> forget_type_decl(TermIn) ; true )
    ;
        Term =.. [Space, '#primitive', TermIn],
        retractall(Term)
    ).

%Add a function atom. A clause that does not translate leaves nothing behind:
'add-atom'(Space, Term, true) :- Term = [=,[FAtom|W],_], !,
                                 length(W, N),
                                 Arity is N + 1,
                                 ( fun(FAtom) -> WasFun = true ; WasFun = false ),
                                 ( arity(FAtom, Arity) -> HadArity = true ; HadArity = false ),
                                 ( nb_current(FAtom, Metas) -> true ; Metas = [] ),
                                 Raw =.. [Space|Term],
                                 assertz(Raw, RawRef),
                                 register_fun(FAtom),
                                 ( HadArity == true -> true ; assertz(arity(FAtom, Arity)) ),
                                 catch(( translate_clause(Term, Clause) -> Status = ok ; Status = failed ), E, Status = error(E)),
                                 ( Status == ok
                                   -> true
                                    ; erase(RawRef),
                                      nb_setval(FAtom, Metas),
                                      ( WasFun == true -> true ; retractall(fun(FAtom)) ),
                                      ( HadArity == true -> true ; retractall(arity(FAtom, Arity)) ),
                                      ( Status = error(Error) -> throw(Error) ; fail ) ),
                                 assertz(Clause, Ref),
                                 assertz(translated_from(Ref, Term)),
                                 metta_on_function_changed(FAtom),
                                 invalidate_specializations(FAtom),
                                 late_function(FAtom),
                                 maybe_print_compiled_clause("added function", Term, Clause).

%Add an atom to the space:
'add-atom'(Space, Term, true) :- add_sexp(Space, Term).

%%Remove a function atom:
'remove-atom'(Space, Term, Removed) :- Term = [=,[F|Args],Body], !,
                                       remove_sexp(Space, Term),
                                       ( atom(F), nb_current(F, Prev) -> true ; Prev = [] ),
                                       (   select(Meta, Prev, Rest),
                                           Meta = fun_meta(Args0, Body0),
                                           Args0 =@= Args,
                                           Body0 =@= Body
                                           -> ( Rest == [] -> nb_delete(F)
                                                            ; nb_setval(F, Rest) ) ; true ),
                                       findall(Ref, translated_from(Ref, Term), Refs),
                                       forall(member(Ref, Refs), erase(Ref)),
                                       retractall(translated_from(_, Term)),
                                       metta_on_function_changed(F),
                                       invalidate_specializations(F),
                                       ( \+ ( current_predicate(F/A), functor(H2, F, A), clause(H2, _, _) )
                                         -> retractall(fun(F)), metta_on_function_removed(F)
                                         ; true ),
                                       ( Refs = [] -> Removed = false ; Removed = true ).

%Remove all same atoms:
'remove-atom'(Space, Term, true) :- remove_sexp(Space, Term).

% A space is a predicate per row arity, created by the first add-atom. Reading
% a space before it is written calls an undefined predicate, and every such
% call would search the autoloader before failing. The first call declares the
% space's predicate dynamic instead, so later reads are plain calls on an empty
% predicate; reads of existing spaces pay nothing extra.
space_call(Term) :- catch(Term, E, space_missing(E, Term)).

space_missing(error(existence_error(procedure, Space/Arity), _), Term) :-
    functor(Term, Space, Arity), !,
    dynamic(Space/Arity),
    fail.

%Match for conjunctive pattern
match(_, LComma, OutPattern, Result) :- LComma == [','], !,
                                        Result = OutPattern.
match(Space, [Comma|[Head|Tail]], OutPattern, Result) :- Comma == ',', !,
                                                         ( is_list(Head) -> append([Space], Head, List), Term =.. List
                                                                          ; Term =.. [Space, '#primitive', Head] ),
                                                         space_call(Term),
                                                         \+ cyclic_term(OutPattern),
                                                         match(Space, [','|Tail], OutPattern, Result).

% When the pattern list itself is a variable -> enumerate all atoms
match(Space, PatternVar, OutPattern, Result) :- var(PatternVar), !,
                                                'get-atoms'(Space, PatternVar),
                                                \+ cyclic_term(OutPattern),
                                                Result = OutPattern.

%Match for pattern:
match(Space, Pattern, OutPattern, Result) :-
    ( is_list(Pattern), Pattern = [Rel|PatArgs] ->
        Term =.. [Space, Rel | PatArgs]
    ;
        Term =.. [Space, '#primitive', Pattern]
    ),
    space_call(Term),
    \+ cyclic_term(OutPattern),
    Result = OutPattern.

%Get all atoms in space, irregard of arity:
'get-atoms'(Space, Pattern) :- current_predicate(Space/Arity),
                               functor(Head, Space, Arity),
                               clause(Head, true),
                               Head =.. [Space | Args],
                               ( Args = ['#primitive', P] -> Pattern = P ; Pattern = Args ).
