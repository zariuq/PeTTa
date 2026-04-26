:- dynamic state_cell/3.

:- multifile 'bind!'/3.
:- multifile 'change-state!'/3.
:- multifile 'get-state'/2.
:- multifile 'new-state'/2.

he_state_handle(Term, Id) :-
    atom(Term),
    atom_prefix(Term, '$state_'),
    atom_concat('$state_', IdAtom, Term),
    atom_number(IdAtom, Id).

he_next_state_id(Id) :-
    flag(metta_state_id, Prev, Prev + 1),
    Id is Prev + 1.

he_make_state(Value, StateHandle) :-
    he_next_state_id(Id),
    format(atom(StateHandle), '$state_~d', [Id]),
    'get-type'(Value, Type0),
    ( Type0 == '%Undefined%' -> Type = 'Atom' ; Type = Type0 ),
    assertz(state_cell(Id, Type, Value)).

he_state_value(Id, Value) :-
    state_cell(Id, _, Value).

he_normalize_state_term(Term, Norm) :-
    he_normalize_state_term_seen(Term, [], Norm).

he_normalize_state_term_seen(Term, _, Norm) :-
    var(Term), !,
    Norm = Term.
he_normalize_state_term_seen(Term, Seen, Norm) :-
    he_space_ref_atom(Term),
    catch(nb_getval(Term, Bound), _, fail),
    he_state_handle(Bound, Id), !,
    ( memberchk(Id, Seen)
    -> Norm = ['new-state', '%Cycle%']
    ; he_state_value(Id, Value0),
      he_normalize_state_term_seen(Value0, [Id|Seen], Value),
      Norm = ['new-state', Value]
    ).
he_normalize_state_term_seen(Term, Seen, Norm) :-
    he_state_handle(Term, Id), !,
    ( memberchk(Id, Seen)
    -> Norm = ['new-state', '%Cycle%']
    ; he_state_value(Id, Value0),
      he_normalize_state_term_seen(Value0, [Id|Seen], Value),
      Norm = ['new-state', Value]
    ).
he_normalize_state_term_seen(Term, _, Norm) :-
    atomic(Term), !,
    Norm = Term.
he_normalize_state_term_seen(Term, Seen, Norm) :-
    is_list(Term), !,
    maplist({Seen}/[X,Y]>>he_normalize_state_term_seen(X, Seen, Y), Term, Norm).
he_normalize_state_term_seen(Term, Seen, Norm) :-
    Term =.. [F|Args],
    maplist({Seen}/[X,Y]>>he_normalize_state_term_seen(X, Seen, Y), Args, ArgsNorm),
    Norm =.. [F|ArgsNorm].

'bind!'(A, B, true) :-
    he_profile_enabled, !,
    he_eval_if_expr(B, V),
    nb_setval(A, V).
'bind!'(A, ['new-state', B], C) :- 'change-state!'(A, B, C).

'new-state'(Value, State) :-
    he_profile_enabled, !,
    he_make_state(Value, State).
'new-state'(Value, ['new-state', Value]).

'change-state!'(Target, Value, Out) :-
    he_profile_enabled, !,
    ( he_space_ref_atom(Target),
      catch(nb_getval(Target, Bound), _, fail)
      -> he_change_state(Bound, Value, Out)
    ; he_change_state(Target, Value, Out)
    ).
'change-state!'(Var, Value, true) :- nb_setval(Var, Value).

he_change_state(State, Value, State) :-
    he_state_handle(State, Id),
    state_cell(Id, Expected, _),
    he_type_accepts(Expected, Value, _), !,
    retractall(state_cell(Id, _, _)),
    assertz(state_cell(Id, Expected, Value)).
he_change_state(State, Value, ['Error', ['change-state!', State, Value], ['BadArgType', 2, Expected, Actual]]) :-
    he_state_handle(State, Id),
    state_cell(Id, Expected, _),
    he_actual_type(Value, Actual), !.
he_change_state(Target, Value, ['Error', ['change-state!', Target, Value], 'BadStateTarget']).

'get-state'(Target, Value) :-
    he_space_ref_atom(Target),
    catch(nb_getval(Target, Bound), _, fail), !,
    'get-state'(Bound, Value).
'get-state'(State, Value) :-
    he_state_handle(State, Id), !,
    he_state_value(Id, Value).
'get-state'(Var, Value) :- nb_getval(Var, Value).
