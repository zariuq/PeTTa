:- dynamic he_space_type/2.
:- dynamic he_eq_fact/4.
:- dynamic he_space_key_count/4.
:- dynamic mork_dump_cache/2.

he_space_fact_key(Term, '$atom', 1) :-
    \+ is_list(Term), !.
he_space_fact_key([Rel], Rel, 1) :-
    atom(Rel), !.
he_space_fact_key([Rel, _], Rel, 2) :-
    atom(Rel), !.
he_space_fact_key([Rel, _, _], Rel, 3) :-
    atom(Rel), !.
he_space_fact_key([Rel, _, _, _], Rel, 4) :-
    atom(Rel), !.
he_space_fact_key([Rel|Args], Rel, Arity) :-
    atom(Rel), !,
    length(Args, TailArity),
    Arity is TailArity + 1.

he_space_pattern_key(Pattern, '$atom', 1) :-
    \+ is_list(Pattern), !.
he_space_pattern_key([Rel], Rel, 1) :-
    atom(Rel), !.
he_space_pattern_key([Rel, _], Rel, 2) :-
    atom(Rel), !.
he_space_pattern_key([Rel, _, _], Rel, 3) :-
    atom(Rel), !.
he_space_pattern_key([Rel, _, _, _], Rel, 4) :-
    atom(Rel), !.
he_space_pattern_key([Rel|Args], Rel, Arity) :-
    atom(Rel), !,
    length(Args, TailArity),
    Arity is TailArity + 1.

he_space_candidate_pattern(Pattern) :-
    nonvar(Pattern),
    \+ is_list(Pattern), !.
he_space_candidate_pattern([Rel|_]) :-
    nonvar(Rel),
    atom(Rel),
    Rel \== ','.

he_space_fact_count_inc(Space, Key, Arity) :-
    ( retract(he_space_key_count(Space, Key, Arity, Count0))
    -> Count is Count0 + 1
    ;  Count = 1
    ),
    assertz(he_space_key_count(Space, Key, Arity, Count)).

he_space_fact_count_dec(Space, Key, Arity) :-
    ( retract(he_space_key_count(Space, Key, Arity, Count0))
    -> Count is Count0 - 1,
       ( Count > 0
       -> assertz(he_space_key_count(Space, Key, Arity, Count))
       ;  true
       )
    ;  true
    ).

he_space_fact_added_hook(Space, Term) :-
    he_space_fact_key(Term, Key, Arity),
    he_space_fact_count_inc(Space, Key, Arity).

he_space_fact_removed_hook(Space, Term) :-
    he_space_fact_key(Term, Key, Arity),
    he_space_fact_count_dec(Space, Key, Arity).

he_space_fact_added_hook('&self', [=, [Fun|HeadArgs], Body]) :-
    atom(Fun), !,
    length(HeadArgs, Arity),
    ( he_eq_fact(Fun, Arity, HeadArgs, Body)
    -> true
    ; assertz(he_eq_fact(Fun, Arity, HeadArgs, Body))
    ).

he_space_fact_removed_hook('&self', [=, [Fun|HeadArgs], Body]) :-
    atom(Fun), !,
    length(HeadArgs, Arity),
    retractall(he_eq_fact(Fun, Arity, HeadArgs, Body)).

he_resolve_space_ref(Space, Resolved) :-
    Space == '&self', !,
    Resolved = '&self'.
he_resolve_space_ref(Space, Resolved) :-
    he_space_ref_atom(Space),
    catch(nb_getval(Space, Bound), _, fail),
    he_space_ref_atom(Bound), !,
    Resolved = Bound.
he_resolve_space_ref(Space, Space).

he_actual_space_target('&self', '&self') :- !.
he_actual_space_target(Space0, Space) :-
    he_resolve_space_ref(Space0, Space),
    Space \== Space0,
    ( Space == '&self'
    ; he_space_type(Space, _)
    ), !.
he_actual_space_target(Space, Space) :-
    he_space_type(Space, _).

'str-length'(S, N) :- string_length(S, N).
'str-concat'(A, B, Out) :-
    term_atom_string(A, SA),
    term_atom_string(B, SB),
    string_concat(SA, SB, Out).
'str-split'(Sep, S, Parts) :-
    term_atom_string(Sep, SSep),
    term_atom_string(S, Text),
    atom_string(SepAtom, SSep),
    atom_string(TextAtom, Text),
    atomic_list_concat(PartAtoms, SepAtom, TextAtom),
    maplist(atom_string, PartAtoms, Parts).
'str-split-whitespace'(S, Parts) :- split_string(S, " \t\n\r", " \t\n\r", Parts).
'str-join'(Sep, Parts, Out) :-
    term_atom_string(Sep, SSep),
    maplist(term_atom_string, Parts, StringParts),
    atomics_to_string(StringParts, SSep, Out).
'str-slice'(S, Start, End, Out) :-
    term_atom_string(S, Text),
    integer(Start),
    integer(End),
    Start >= 0,
    End >= Start,
    string_length(Text, Len0),
    SliceStart is min(Start, Len0),
    SliceEnd is min(End, Len0),
    SliceLen is max(0, SliceEnd - SliceStart),
    sub_string(Text, SliceStart, SliceLen, _, Out).
'str-find'(S, Needle, Out) :-
    term_atom_string(S, Text),
    term_atom_string(Needle, Pattern),
    ( sub_string(Text, Index, _, _, Pattern)
    -> Out = Index
    ;  Out = 'Empty'
    ).
'str-starts-with?'(S, Prefix, Out) :-
    term_atom_string(S, Text),
    term_atom_string(Prefix, Wanted),
    ( sub_string(Text, 0, _, _, Wanted)
    -> Out = true
    ;  Out = false
    ).
'str-ends-with?'(S, Suffix, Out) :-
    term_atom_string(S, Text),
    term_atom_string(Suffix, Wanted),
    ( string_concat(_, Wanted, Text)
    -> Out = true
    ;  Out = false
    ).
'str-trim'(S, Out) :-
    string_codes(S, Codes),
    trim_space_codes(Codes, Trimmed),
    string_codes(Out, Trimmed).

trim_space_codes(Codes, Trimmed) :-
    drop_space_prefix(Codes, Front),
    reverse(Front, Rev),
    drop_space_prefix(Rev, Back),
    reverse(Back, Trimmed).

drop_space_prefix([C|Cs], Rest) :-
    code_type(C, space), !,
    drop_space_prefix(Cs, Rest).
drop_space_prefix(Cs, Cs).

'fs-exists?'(Spec, Result) :-
    term_atom_string(Spec, S),
    ( resolve_existing_data_file(S, _) -> Result = true ; Result = false ).
'fs-read-lines'(Spec, Lines) :-
    term_atom_string(Spec, S),
    resolve_existing_data_file(S, Path),
    read_file_to_string(Path, Text, []),
    split_string(Text, "\n", "\r", Raw),
    drop_final_empty(Raw, Lines).
'fs-read-text'(Spec, Text) :-
    term_atom_string(Spec, S),
    resolve_existing_data_file(S, Path),
    read_file_to_string(Path, Text, []).
'fs-resolve-path'(Spec, Path) :-
    term_atom_string(Spec, S),
    ( resolve_existing_data_file(S, Resolved)
    -> Path = Resolved
    ;  Path = S
    ).

drop_final_empty(Lines, Trimmed) :-
    append(Trimmed, [""], Lines), !.
drop_final_empty(Lines, Lines).

'system-cwd'(Cwd) :-
    working_directory(Dir, Dir),
    atom_string(Dir, Cwd).
'system-has-args'(false).
nop(_, []).

he_next_space_id(Id) :-
    flag(metta_space_id, Prev, Prev + 1),
    Id is Prev + 1.

he_make_space(Type, Space) :-
    he_next_space_id(Id),
    format(atom(Space), '&space_~d', [Id]),
    assertz(he_space_type(Space, Type)).

'new-space'(Space) :- he_make_space('Space', Space).
'new-space'(Kind, Space) :- he_make_space(['Space', Kind], Space).

he_bound_space_type(X, T) :-
    he_space_ref_atom(X),
    catch(nb_getval(X, Bound), _, fail),
    atom(Bound),
    he_space_type(Bound, T).

he_space_may_have_match(_Space, Pattern) :-
    var(Pattern), !.
he_space_may_have_match(_Space, [Rel|_]) :-
    var(Rel), !.
he_space_may_have_match(_Space, [','|_]) :- !.
he_space_may_have_match('&self', [':', Fun, Type]) :-
    nonvar(Fun), !,
    he_type_fact(Fun, Type).
he_space_may_have_match('&self', [=, [Fun|HeadArgs], Body]) :-
    atom(Fun), !,
    length(HeadArgs, Arity),
    he_eq_fact(Fun, Arity, HeadArgs, Body).
he_space_may_have_match(Space, Pattern) :-
    he_space_pattern_key(Pattern, Key, Arity), !,
    he_space_key_count(Space, Key, Arity, Count),
    Count > 0.
he_space_may_have_match(_, _).

he_space_exact_member(Space, Pattern) :-
    he_perf_counter_inc(space_exact_member_calls),
    ground(Pattern),
    he_space_may_have_match(Space, Pattern),
    ( is_list(Pattern)
    -> Term =.. [Space|Pattern]
    ;  Term =.. [Space, Pattern]
    ),
    catch(call(Term), _, fail),
    he_perf_counter_inc(space_exact_member_hits).

he_space_candidate_atom(Space, Pattern, Candidate) :-
    he_space_candidate_pattern(Pattern),
    he_space_may_have_match(Space, Pattern), !,
    copy_term(Pattern, Candidate),
    ( is_list(Candidate)
    -> Term =.. [Space|Candidate]
    ;  Term =.. [Space, Candidate]
    ),
    catch(call(Term), _, fail),
    he_perf_counter_inc(space_candidate_index_hits).
he_space_candidate_atom(Space, _Pattern, Candidate) :-
    he_perf_counter_inc(space_candidate_scan_fallbacks),
    he_space_atom(Space, Candidate).

he_space_candidate_equation(Space, Call, StoredHead, StoredBody) :-
    he_space_candidate_atom(Space,
                            [=, Call, StoredBody],
                            [=, StoredHead, StoredBody]),
    is_list(StoredHead).

he_count_atoms(Space0, Count) :-
    he_profile_enabled,
    he_space_ref_atom(Space0),
    \+ he_actual_space_target(Space0, _), !,
    Count = ['count-atoms', Space0].
he_count_atoms(Space0, Count) :-
    he_resolve_space_ref(Space0, Space),
    findall(Atom, he_space_atom(Space, Atom), Atoms),
    length(Atoms, Count).

'count-atoms'(Space, Count) :- he_count_atoms(Space, Count).
size(Space, Count) :-
    he_space_ref_atom(Space), !,
    he_count_atoms(Space, Count).
size(List, Count) :- is_list(List), !, length(List, Count).
size(_, 1).

he_space_kind(Space, Kind) :-
    ( he_space_type(Space, ['Space', Kind0])
    -> Kind = Kind0
    ; he_space_type(Space, 'Space')
    -> Kind = plain
    ; Kind = plain
    ).

he_ordered_space_kind(queue).
he_ordered_space_kind(stack).

he_ordered_space_empty_error(queue, 'EmptyQueueSpace').
he_ordered_space_empty_error(stack, 'EmptyStackSpace').

he_space_atoms_list(Space0, Atoms) :-
    he_resolve_space_ref(Space0, Space),
    findall(Atom, he_space_atom(Space, Atom), Atoms).

he_replace_space_atoms(Space0, NewAtoms) :-
    he_resolve_space_ref(Space0, Space),
    he_space_atoms_list(Space, OldAtoms),
    forall(member(Atom, OldAtoms),
           ( remove_sexp(Space, Atom),
             he_note_space_fact_removed(Space, Atom)
           )),
    forall(member(Atom, NewAtoms),
           ( add_sexp(Space, Atom),
             he_note_space_fact_added(Space, Atom)
           )).

he_ordered_space_resolved(Space0, Surface, Space, Kind) :-
    he_resolve_space_ref(Space0, Space),
    he_space_kind(Space, Kind),
    ( he_ordered_space_kind(Kind)
    -> true
    ;  throw(he_surface_error(['Error', [Surface, Space0], 'UnsupportedSpaceKind']))
    ).

he_nonnegative_index(Index) :-
    integer(Index),
    Index >= 0.

'space-len'(Space0, Count) :-
    he_count_atoms(Space0, Count).

'space-push'(Space0, Term, Out) :-
    catch(
        ( he_ordered_space_resolved(Space0, 'space-push', Space, _Kind),
          add_sexp(Space, Term),
          he_note_space_fact_added(Space, Term),
          he_bridge_result([], true, Out)
        ),
        he_surface_error(Error),
        Out = Error
    ).

'space-peek'(Space0, Out) :-
    catch(
        ( he_ordered_space_resolved(Space0, 'space-peek', Space, Kind),
          he_space_atoms_list(Space, Atoms),
          ( Kind == queue
          -> ( Atoms = [Out|_] -> true ; true )
          ;  ( append(_, [Out], Atoms) -> true ; true )
          )
        ),
        he_surface_error(Error),
        Out = Error
    ),
    ( var(Out)
    -> he_ordered_space_resolved(Space0, 'space-peek', _, Kind),
       he_ordered_space_empty_error(Kind, EmptyError),
       Out = ['Error', ['space-peek', Space0], EmptyError]
    ; true
    ).

'space-pop'(Space0, Out) :-
    catch(
        ( he_ordered_space_resolved(Space0, 'space-pop', Space, Kind),
          he_space_atoms_list(Space, Atoms),
          ( Kind == queue
          -> ( Atoms = [Out|Rest] -> true ; Rest = Atoms )
          ;  ( append(Rest, [Out], Atoms) -> true ; Rest = Atoms )
          ),
          ( var(Out)
          -> true
          ;  he_replace_space_atoms(Space, Rest)
          )
        ),
        he_surface_error(Error),
        Out = Error
    ),
    ( var(Out)
    -> he_ordered_space_resolved(Space0, 'space-pop', _, Kind),
       he_ordered_space_empty_error(Kind, EmptyError),
       Out = ['Error', ['space-pop', Space0], EmptyError]
    ; true
    ).

'space-get'(Space0, Index, Out) :-
    catch(
        ( he_ordered_space_resolved(Space0, 'space-get', Space, _Kind),
          ( he_nonnegative_index(Index)
          -> he_space_atoms_list(Space, Atoms),
             ( nth0(Index, Atoms, Out)
             -> true
             ;  Out = ['Error', ['space-get', Space0, Index], 'IndexOutOfBounds']
             )
          ;  Out = ['Error', ['space-get', Space0, Index], 'ExpectedNonNegativeIndex']
          )
        ),
        he_surface_error(Error),
        Out = Error
    ).

'space-truncate'(Space0, Index, Out) :-
    catch(
        ( he_ordered_space_resolved(Space0, 'space-truncate', Space, _Kind),
          ( he_nonnegative_index(Index)
          -> he_space_atoms_list(Space, Atoms),
             length(Atoms, Len),
             ( Index =< Len
             -> length(Kept, Index),
                append(Kept, _, Atoms),
                he_replace_space_atoms(Space, Kept),
                he_bridge_result([], true, Out)
             ;  Out = ['Error', ['space-truncate', Space0, Index], 'IndexOutOfBounds']
             )
          ;  Out = ['Error', ['space-truncate', Space0, Index], 'ExpectedNonNegativeIndex']
          )
        ),
        he_surface_error(Error),
        Out = Error
    ).

'sealed'(_Vars, Expr, Out) :-
    he_profile_enabled,
    copy_term(Expr, Out).

'add-atom-nodup'(Space0, Term, Out) :-
    he_resolve_space_ref(Space0, Space),
    ( he_space_exact_member(Space, Term)
    -> he_perf_counter_inc(space_add_if_absent_exact_present)
    ; once(match(Space, Term, Term, _))
    -> he_perf_counter_inc(space_add_if_absent_match_present)
    ; 'add-atom'(Space, Term, _),
      he_perf_counter_inc(space_add_if_absent_added)
    ),
    ( he_profile_enabled -> Out = [] ; Out = true ).

he_match_once_truth_list(Space0, Pattern, Out) :-
    he_resolve_space_ref(Space0, Space),
    ( he_space_exact_member(Space, Pattern)
    -> Out = [true]
    ; once(match(Space, Pattern, true, _))
    -> Out = [true]
    ; Out = []
    ).

he_space_has_ground_atom(Space, Pattern) :-
    he_space_exact_member(Space, Pattern).

he_match_once_truth_empty(Space0, Pattern, Out) :-
    he_resolve_space_ref(Space0, Space),
    ( he_space_exact_member(Space, Pattern)
    -> Out = false
    ; once(match(Space, Pattern, true, _))
    -> Out = false
    ; Out = true
    ).

he_match_once_pattern_empty(Space0, Pattern, Out) :-
    he_resolve_space_ref(Space0, Space),
    ( he_space_exact_member(Space, Pattern)
    -> Out = false
    ; once(match(Space, Pattern, Pattern, _))
    -> Out = false
    ; Out = true
    ).

he_make_space_snapshot(Space0, Snapshot) :-
    he_resolve_space_ref(Space0, Space),
    ( he_space_type(Space, Type) -> true ; Type = 'Space' ),
    he_make_space(Type, Snapshot),
    forall(he_space_atom(Space, Atom), add_sexp(Snapshot, Atom)).

he_valid_snapshot_space(Space0, Space) :-
    he_resolve_space_ref(Space0, Space),
    ( Space == '&self'
    ; he_space_ref_atom(Space)
    ).

he_with_space_snapshot(Snapshot, Space, BodyConj, BodyOut, Out) :-
    he_make_space_snapshot(Space, Snapshot),
    BodyConj,
    Out = BodyOut.

he_with_space_snapshot_or_self(Snapshot, _SpaceExpr, Space0, _BodyExpr, BodyConj, BodyOut, Out) :-
    he_valid_snapshot_space(Space0, Space), !,
    he_with_space_snapshot(Snapshot, Space, BodyConj, BodyOut, Out).
he_with_space_snapshot_or_self(Snapshot, SpaceExpr, _Space0, BodyExpr, _BodyConj, _BodyOut, Out) :-
    Out = ['with-space-snapshot', Snapshot, SpaceExpr, BodyExpr].

'mork:new-space'(Space) :- he_make_space('MorkSpace', Space).
'mork:new-space'(_, Space) :- he_make_space('MorkSpace', Space).
'mork:add-atom'(Space, Term, Out) :- 'add-atom-nodup'(Space, Term, Out).
'mork:match'(Space, Pattern, Body, Out) :- match(Space, Pattern, Body, Out).
'mork:size'(Space, Count) :- he_count_atoms(Space, Count).
'mork:get-atoms'(Space0, Atom) :-
    he_resolve_space_ref(Space0, Space),
    he_space_atom(Space, Atom).
'mork:clone'(Space0, Clone) :-
    he_resolve_space_ref(Space0, Space),
    ( he_space_type(Space, Type) -> true ; Type = 'MorkSpace' ),
    he_make_space(Type, Clone),
    forall(he_space_atom(Space, Atom), add_sexp(Clone, Atom)).
'mork:step!'(_, N, N).

he_mork_path(Path, Abs) :-
    term_atom_string(Path, PathString),
    ( is_absolute_file_name(PathString)
    -> Abs = PathString
    ; current_import_base(Base),
      directory_file_path(Base, PathString, Candidate),
      absolute_file_name(Candidate, Abs, [file_errors(fail)])
    ).

'mork:dump!'(Space0, Path, []) :-
    he_resolve_space_ref(Space0, Space),
    he_mork_path(Path, Abs),
    findall(Atom, he_space_atom(Space, Atom), Atoms),
    retractall(mork_dump_cache(Abs, _)),
    assertz(mork_dump_cache(Abs, Atoms)),
    catch(setup_call_cleanup(open(Abs, write, Stream),
                             forall(member(Atom, Atoms),
                                    ( writeq(Stream, Atom),
                                      write(Stream, '.\n') )),
                             close(Stream)),
          _, true).

'mork:open-act'(Path, Space) :-
    he_mork_path(Path, Abs),
    he_make_space('MorkSpace', Space),
    ( mork_dump_cache(Abs, Atoms)
    -> true
    ; catch(setup_call_cleanup(open(Abs, read, Stream),
                               read_mork_atoms(Stream, Atoms),
                               close(Stream)),
            _, Atoms = [])
    ),
    forall(member(Atom, Atoms), add_sexp(Space, Atom)).

read_mork_atoms(Stream, Atoms) :-
    read(Stream, Term),
    ( Term == end_of_file
    -> Atoms = []
    ; Atoms = [Term|Rest],
      read_mork_atoms(Stream, Rest)
    ).

quot(A, B, R) :- he_profile_enabled, R is A // B.
rem(A, B, R) :- he_profile_enabled, R is A rem B.
divmod(A, B, [Q, R]) :- he_profile_enabled, Q is A // B, R is A rem B.
'math.quot'(A, B, R) :- he_profile_enabled, R is A // B.
'math.rem'(A, B, R) :- he_profile_enabled, R is A rem B.
'math.mod'(A, B, R) :- he_profile_enabled, R is A mod B.
'math.divmod'(A, B, [Q, R]) :- he_profile_enabled, Q is A // B, R is A rem B.
