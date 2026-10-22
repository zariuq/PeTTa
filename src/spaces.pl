%Since both normal add-attom call and function additions needs to add the S-expression.
%The atoms of &self also maintain the declarations the compiler reads (types.pl):
%A declaration the compiler rejects is not stored:
add_sexp(Space, TermIn) :-
    ( is_list(TermIn), TermIn = [Rel|Args] ->
        Term =.. [Space, Rel | Args],
        store_row(Term),
        ( Space == '&self' -> catch(note_type_decl(TermIn), E, ( ignore(retract(Term)), throw(E) )) ; true )
    ;
        Term =.. [Space, '#primitive', TermIn],
        store_row(Term)
    ).

%A stored atom keeps the held checks of its open parts (types.pl): each read
%of it is a fresh copy with the same constraints.
store_row(Term) :- ( held_active, \+ ground(Term), term_attvars(Term, [_|_])
                     -> held_transport(Term, Plain, Gs), assertz((Plain :- types:held_restore(Gs)))
                     ; assertz(Term) ).

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
'add-atom'(Space, Term0, true) :- Term0 = [=,[FAtom|W],_], !, space_row(Space, Term0),
                                 %an equation holding checked open values keeps their checks:
                                 %each call restores them on its fresh copy
                                 ( held_active, term_attvars(Term0, [_|_]) -> held_transport(Term0, Term, Held),
                                                                               assertz(types:held_function(FAtom))
                                 ; Term = Term0, Held = [] ),
                                 length(W, N),
                                 Arity is N + 1,
                                 ( fun(FAtom) -> WasFun = true ; WasFun = false ),
                                 ( arity(FAtom, Arity) -> HadArity = true ; HadArity = false ),
                                 ( nb_current(FAtom, Metas) -> true ; Metas = [] ),
                                 Raw =.. [Space|Term],
                                 ( Held == [] -> assertz(Raw, RawRef) ; assertz((Raw :- types:held_restore(Held)), RawRef) ),
                                 register_fun(FAtom),
                                 ( HadArity == true -> true ; assertz(arity(FAtom, Arity)) ),
                                 catch(( translate_clause(Term, Clauses) -> Status = ok ; Status = failed ), E, Status = error(E)),
                                 ( Status == ok
                                   -> true
                                    ; erase(RawRef),
                                      nb_setval(FAtom, Metas),
                                      ( WasFun == true -> true ; retractall(fun(FAtom)) ),
                                      ( HadArity == true -> true ; retractall(arity(FAtom, Arity)) ),
                                      ( Status = error(Error) -> throw(Error) ; fail ) ),
                                 ( Held == [] -> Clauses1 = Clauses
                                 ; maplist({Held}/[(H :- B), (H :- (types:held_restore(Held), B))]>>true, Clauses, Clauses1) ),
                                 assert_translated(Term, Clauses1, _),
                                 forall(metta_on_function_changed(FAtom), true),
                                 invalidate_specializations(FAtom),
                                 late_function(FAtom),
                                 types:recompile_stale,
                                 maybe_print_compiled_clause("added function", Term, Clauses).

%Add an atom to the space; a space declared (SpaceOf Row) takes rows of Row only
%(see types.pl):
'add-atom'(Space, Term, true) :- space_row(Space, Term), add_sexp(Space, Term).

%%Remove a function atom:
'remove-atom'(Space, Term, Removed) :- Term = [=,[F|Args],Body], !,
                                       remove_sexp(Space, Term),
                                       ( atom(F), nb_current(F, Prev) -> true ; Prev = [] ),
                                       (   select(Meta, Prev, Rest),
                                           Meta = fun_meta(Args0, _, _, Body0),
                                           [Args0, Body0] =@= [Args, Body]
                                           -> ( Rest == [] -> nb_delete(F)
                                                            ; nb_setval(F, Rest) ) ; true ),
                                       findall(Ref, ( translated_from(Ref, T), ( T = Term ; T = saturated(Term) ) ), Refs),
                                       forall(member(Ref, Refs), ( erase(Ref), retractall(translated_from(Ref, _)) )),
                                       forall(metta_on_function_changed(F), true),
                                       invalidate_specializations(F),
                                       ( \+ ( current_predicate(F/A), functor(H2, F, A), clause(H2, _, _) )
                                         -> retractall(fun(F)), forall(metta_on_function_removed(F), true)
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
%Any other error (a type error of a row's held check, say) is the read's error:
space_missing(E, _) :- throw(E).

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
                               clause(Head, Body), call(Body),
                               Head =.. [Space | Args],
                               ( Args = ['#primitive', P] -> Pattern = P ; Pattern = Args ).
