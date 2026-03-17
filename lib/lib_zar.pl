%% lib_zar.pl - shared Prolog helpers for PeTTa demos
%%
%% Consolidated utilities:
%%   - FFI profiling and specialized space backends
%%   - command-line helpers shared by MeTTa scripts
%%   - job TSV parsing (used by batched selectors)
%%   - numerically stable math kernels (used by PLN scoring hot paths)
%%
%% Intentionally non-module style so existing `(consult)` + `import_prolog_function`
%% flows can import predicates directly without module qualification.

:- use_module(library(readutil)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).

%% ======================================================================
%% FFI Call Profiling — lightweight counters
%% ======================================================================
%% Uses nb_setval (non-backtrackable globals) for O(1) increment.
%% Shared by lib_zar.pl (sp_*) and pverify_ds.pl (ds_*).

:- dynamic ffi_counter_names/1.
:- dynamic ffi_profiling_enabled/0.
ffi_counter_names([]).

ffi_counter_init(ok) :-
    retractall(ffi_counter_names(_)),
    assert(ffi_counter_names([])),
    assert(ffi_profiling_enabled).

ffi_counter_init_off(ok) :-
    retractall(ffi_profiling_enabled).

ffi_inc(Name) :-
    ( ffi_profiling_enabled ->
        ( nb_current(Name, Old) ->
            New is Old + 1,
            nb_setval(Name, New)
        ;   nb_setval(Name, 1),
            retract(ffi_counter_names(Names)),
            assert(ffi_counter_names([Name|Names]))
        )
    ; true
    ).

ffi_counter_dump(ok) :-
    ffi_counter_names(Names),
    sort(Names, Sorted),
    format("~n=== FFI Call Counts ===~n"),
    ffi_dump_total(Sorted, 0, Total),
    format("~nTotal FFI calls: ~w~n", [Total]).

ffi_dump_total([], Total, Total).
ffi_dump_total([Name|Rest], Acc, Total) :-
    nb_getval(Name, Count),
    format("  ~w: ~w~n", [Name, Count]),
    Acc1 is Acc + Count,
    ffi_dump_total(Rest, Acc1, Total).

%% ============================================================================
%% Shared IO helpers
%% ============================================================================

get_cmdline_filter_internal([], []).
get_cmdline_filter_internal([Arg|Rest], Filtered) :-
    ( Arg == '--silent'
    ; Arg == mork
    ),
    !,
    get_cmdline_filter_internal(Rest, Filtered).
get_cmdline_filter_internal([Arg|Rest], [Arg|Tail]) :-
    get_cmdline_filter_internal(Rest, Tail).

get_cmdline_args(Args) :-
    current_prolog_flag(argv, RawArgs),
    ( RawArgs = [_File|Rest] -> UserRaw = Rest ; UserRaw = [] ),
    get_cmdline_filter_internal(UserRaw, Args).

get_cmdline_arg(Index, Arg) :-
    get_cmdline_args(Args),
    ( nth0(Index, Args, A)
    -> Arg = A
    ;  Arg = 'Empty'
    ).

%% Back-compat alias for older selector code.
get_cmdline(Index, Arg) :-
    get_cmdline_arg(Index, Arg).

cmdline_arg_count(Count) :-
    get_cmdline_args(Args),
    length(Args, Count).

has_cmdline_args(true) :-
    get_cmdline_args(Args),
    Args \= [], !.
has_cmdline_args(false).

skip_line(Line) :-
    split_string(Line, " \t", " \t\r", Parts),
    ( Parts = []
    ; Parts = [H|_],
      sub_string(H, 0, 1, _, "#")
    ).

read_lines(Filename, Lines) :-
    read_file_to_string(Filename, Content, []),
    split_string(Content, "\n", "", Lines).

%% query_id<TAB>axiom
parse_axiom_queries_file(Filename, Rows) :-
    read_lines(Filename, Lines),
    parse_axiom_query_lines(Lines, Rows).

parse_axiom_query_lines([], []).
parse_axiom_query_lines([Line|Rest], Rows) :-
    ( skip_line(Line)
    -> parse_axiom_query_lines(Rest, Rows)
    ; ( parse_axiom_query_line(Line, Row)
      -> Rows = [Row|Tail],
         parse_axiom_query_lines(Rest, Tail)
      ;  parse_axiom_query_lines(Rest, Rows)
      )
    ).

parse_axiom_query_line(Line, [QueryId, Axiom]) :-
    split_string(Line, "\t", " \t\r", [QueryIdS, AxiomS]),
    atom_string(QueryId, QueryIdS),
    atom_string(Axiom, AxiomS).

to_atoms([], []).
to_atoms([S|Rest], [A|ATail]) :-
    atom_string(A, S),
    to_atoms(Rest, ATail).

to_numbers([], []).
to_numbers([S|Rest], [N|NTail]) :-
    number_string(N, S),
    to_numbers(Rest, NTail).

%% Back-compat aliases used by existing selectors
is_get_cmdline(Index, Arg) :-
    get_cmdline_arg(Index, Arg).
is_skip_line(Line) :-
    skip_line(Line).
is_read_lines(Filename, Lines) :-
    read_lines(Filename, Lines).
is_parse_axiom_queries_file(Filename, Rows) :-
    parse_axiom_queries_file(Filename, Rows).
is_to_atoms(In, Out) :-
    to_atoms(In, Out).
is_to_numbers(In, Out) :-
    to_numbers(In, Out).
zar_get_cmdline_arg(Index, Arg) :-
    get_cmdline_arg(Index, Arg).
zar_skip_line(Line) :-
    skip_line(Line).
zar_io_get_cmdline_arg(Index, Arg) :-
    get_cmdline_arg(Index, Arg).
zar_io_skip_line(Line) :-
    skip_line(Line).
zar_io_read_lines(Filename, Lines) :-
    read_lines(Filename, Lines).
zar_io_parse_axiom_queries_file(Filename, Rows) :-
    parse_axiom_queries_file(Filename, Rows).
zar_io_to_atoms(In, Out) :-
    to_atoms(In, Out).
zar_io_to_numbers(In, Out) :-
    to_numbers(In, Out).

% new-space / delete-space: dynamic space creation via gensym
% Workaround for PeTTa compiler not handling new-space inside function bodies
'new-space'(SpaceAtom) :- gensym('&zar_space_', SpaceAtom).

'delete-space'(Space, true) :-
    atom(Space),
    forall(
        current_predicate(Space/Arity),
        abolish(Space/Arity)
    ).

%% ======================================================================
%% Specialized Space Backends — MapSpace + SetSpace
%% ======================================================================
%%
%% Dual interface:
%%   1. Normal PeTTa space API (add-atom, match, get-atoms, remove-atom)
%%   2. Optimized O(log n) accessors via AVL/ordset sidecars

%% Space registry — tracks which spaces are maps vs sets
:- dynamic sp_type/2.        % sp_type(SpaceAtom, map|set)
:- dynamic sp_index/2.       % legacy fallback index storage
:- dynamic sp_index_key/2.   % sp_index_key(SpaceAtom, NBGlobalKey)
:- dynamic sp_mode/2.        % sp_mode(SpaceAtom, canonical|index_only)

%% Resolve mode with backward-compatible default.
sp_space_mode(SpaceAtom, Mode) :-
    ( sp_mode(SpaceAtom, M) -> Mode = M ; Mode = canonical ).

%% Fast index storage helpers:
%% Prefer nb_setval/nb_getval via sp_index_key; fall back to dynamic sp_index/2.
sp_make_index_key(SpaceAtom, Key) :-
    atom_concat('__sp_idx_', SpaceAtom, Key).

sp_get_space_index(SpaceAtom, Index) :-
    ( sp_index_key(SpaceAtom, Key)
    -> nb_getval(Key, Index)
    ;  sp_index(SpaceAtom, Index)
    ).

sp_set_space_index(SpaceAtom, NewIndex) :-
    ( sp_index_key(SpaceAtom, Key)
    -> nb_linkval(Key, NewIndex)
    ;  retract(sp_index(SpaceAtom, _)),
       assert(sp_index(SpaceAtom, NewIndex))
    ).

%% ======================================================================
%% MapSpace — key->value store
%% ======================================================================
%% Canonical atoms: SpaceAtom(kv, Key, Value)
%% Internal index:  AVL assoc (Key -> Value)

%% sp_new_map(-SpaceAtom)
sp_new_map(SpaceAtom) :-
    ffi_inc(sp_new_map),
    gensym('&map_', SpaceAtom),
    empty_assoc(Empty),
    sp_make_index_key(SpaceAtom, Key),
    nb_linkval(Key, Empty),
    assert(sp_type(SpaceAtom, map)),
    assert(sp_index_key(SpaceAtom, Key)),
    assert(sp_mode(SpaceAtom, canonical)),
    true.

%% sp_new_map_fast(-SpaceAtom)
%% Index-only mode for high-throughput workloads (no canonical atom mirroring).
sp_new_map_fast(SpaceAtom) :-
    ffi_inc(sp_new_map_fast),
    gensym('&mapf_', SpaceAtom),
    empty_assoc(Empty),
    sp_make_index_key(SpaceAtom, Key),
    nb_linkval(Key, Empty),
    assert(sp_type(SpaceAtom, map)),
    assert(sp_index_key(SpaceAtom, Key)),
    assert(sp_mode(SpaceAtom, index_only)),
    true.

%% sp_map_get(+SpaceAtom, +Key, -Value)
%% O(log n) lookup. Returns not_found if missing.
sp_map_get(SpaceAtom, Key, Value) :-
    ffi_inc(sp_map_get),
    sp_get_space_index(SpaceAtom, Assoc),
    ( get_assoc(Key, Assoc, Value) -> true ; Value = not_found ).

%% sp_map_put(+SpaceAtom, +Key, +Value, -Ok)
sp_map_put(SpaceAtom, Key, Value, ok) :-
    ffi_inc(sp_map_put),
    sp_get_space_index(SpaceAtom, OldAssoc),
    put_assoc(Key, OldAssoc, Value, NewAssoc),
    sp_set_space_index(SpaceAtom, NewAssoc),
    sp_space_mode(SpaceAtom, Mode),
    ( Mode = canonical ->
        ( get_assoc(Key, OldAssoc, OldVal)
        -> ( OldTerm =.. [SpaceAtom, kv, Key, OldVal],
             retractall(OldTerm) )
        ;  true
        ),
        NewTerm =.. [SpaceAtom, kv, Key, Value],
        assertz(NewTerm)
    ; true
    ).

%% sp_map_has(+SpaceAtom, +Key, -Bool)
sp_map_has(SpaceAtom, Key, Bool) :-
    ffi_inc(sp_map_has),
    sp_get_space_index(SpaceAtom, Assoc),
    ( get_assoc(Key, Assoc, _) -> Bool = true ; Bool = false ).

%% sp_map_del(+SpaceAtom, +Key, -Ok)
sp_map_del(SpaceAtom, Key, ok) :-
    ffi_inc(sp_map_del),
    sp_get_space_index(SpaceAtom, OldAssoc),
    ( del_assoc(Key, OldAssoc, _OldValIgnored, NewAssoc)
    -> true
    ;  NewAssoc = OldAssoc
    ),
    sp_space_mode(SpaceAtom, Mode),
    ( Mode = canonical ->
        ( get_assoc(Key, OldAssoc, OldVal)
        -> ( OldTerm =.. [SpaceAtom, kv, Key, OldVal],
             retractall(OldTerm) )
        ; true
        )
    ; true
    ),
    sp_set_space_index(SpaceAtom, NewAssoc).

%% ======================================================================
%% SetSpace — unordered set with O(log n) membership
%% ======================================================================
%% Canonical atoms: SpaceAtom(member, Elem)
%% Internal index:  ordset (sorted list)

%% sp_new_set(-SpaceAtom)
sp_new_set(SpaceAtom) :-
    ffi_inc(sp_new_set),
    gensym('&set_', SpaceAtom),
    sp_make_index_key(SpaceAtom, Key),
    nb_linkval(Key, []),
    assert(sp_type(SpaceAtom, set)),
    assert(sp_index_key(SpaceAtom, Key)),
    assert(sp_mode(SpaceAtom, canonical)),
    true.

%% sp_new_set_fast(-SpaceAtom)
%% Index-only mode for high-throughput workloads (no canonical atom mirroring).
sp_new_set_fast(SpaceAtom) :-
    ffi_inc(sp_new_set_fast),
    gensym('&setf_', SpaceAtom),
    sp_make_index_key(SpaceAtom, Key),
    nb_linkval(Key, []),
    assert(sp_type(SpaceAtom, set)),
    assert(sp_index_key(SpaceAtom, Key)),
    assert(sp_mode(SpaceAtom, index_only)),
    true.

%% sp_set_add(+SpaceAtom, +Elem, -Ok)
sp_set_add(SpaceAtom, Elem, ok) :-
    ffi_inc(sp_set_add),
    sp_get_space_index(SpaceAtom, OldSet),
    ( ord_memberchk(Elem, OldSet)
    -> NewSet = OldSet
    ;  ord_add_element(OldSet, Elem, NewSet),
       sp_space_mode(SpaceAtom, Mode),
       ( Mode = canonical ->
           ( NewTerm =.. [SpaceAtom, member, Elem],
             assertz(NewTerm) )
       ; true
       )
    ),
    sp_set_space_index(SpaceAtom, NewSet).

%% sp_set_has(+SpaceAtom, +Elem, -Bool)
sp_set_has(SpaceAtom, Elem, Bool) :-
    ffi_inc(sp_set_has),
    sp_get_space_index(SpaceAtom, Set),
    ( ord_memberchk(Elem, Set) -> Bool = true ; Bool = false ).

%% sp_set_del(+SpaceAtom, +Elem, -Ok)
sp_set_del(SpaceAtom, Elem, ok) :-
    ffi_inc(sp_set_del),
    sp_get_space_index(SpaceAtom, OldSet),
    ( ord_memberchk(Elem, OldSet)
    -> ord_subtract(OldSet, [Elem], NewSet),
       sp_space_mode(SpaceAtom, Mode),
       ( Mode = canonical ->
           ( OldTerm =.. [SpaceAtom, member, Elem],
             retractall(OldTerm) )
       ; true
       )
    ;  NewSet = OldSet
    ),
    sp_set_space_index(SpaceAtom, NewSet).

%% sp_set_union(+SpaceAtom, +OtherSpaceAtom, -Ok)
sp_set_union(SpaceAtom, OtherAtom, ok) :-
    ffi_inc(sp_set_union),
    sp_get_space_index(SpaceAtom, MySet),
    sp_get_space_index(OtherAtom, TheirSet),
    ord_union(MySet, TheirSet, Merged),
    sp_space_mode(SpaceAtom, Mode),
    ( Mode = canonical ->
        ord_subtract(Merged, MySet, NewElems),
        forall(
            member(E, NewElems),
            ( T =.. [SpaceAtom, member, E], assertz(T) )
        )
    ; true
    ),
    sp_set_space_index(SpaceAtom, Merged).

%% sp_set_subtract(+SpaceAtom, +OtherSpaceAtom, -Ok)
sp_set_subtract(SpaceAtom, OtherAtom, ok) :-
    ffi_inc(sp_set_subtract),
    sp_get_space_index(SpaceAtom, MySet),
    sp_get_space_index(OtherAtom, TheirSet),
    ord_subtract(MySet, TheirSet, Remaining),
    sp_space_mode(SpaceAtom, Mode),
    ( Mode = canonical ->
        ord_subtract(MySet, Remaining, Removed),
        forall(
            member(E, Removed),
            ( T =.. [SpaceAtom, member, E], retractall(T) )
        )
    ; true
    ),
    sp_set_space_index(SpaceAtom, Remaining).

%% sp_set_from_list(+SpaceAtom, +List, -Ok)
sp_set_from_list(SpaceAtom, List, ok) :-
    ffi_inc(sp_set_from_list),
    sp_get_space_index(SpaceAtom, OldSet),
    list_to_ord_set(List, ListSet),
    ord_union(OldSet, ListSet, NewSet),
    sp_space_mode(SpaceAtom, Mode),
    ( Mode = canonical ->
        ord_subtract(NewSet, OldSet, NewElems),
        forall(
            member(E, NewElems),
            ( T =.. [SpaceAtom, member, E], assertz(T) )
        )
    ; true
    ),
    sp_set_space_index(SpaceAtom, NewSet).

%% ======================================================================
%% Opaque index accessors
%% ======================================================================

%% sp_get_index(+SpaceAtom, -Index)
sp_get_index(SpaceAtom, Index) :-
    ffi_inc(sp_get_index),
    sp_get_space_index(SpaceAtom, Index).

%% sp_set_index(+SpaceAtom, +NewIndex, -Ok)
%% Does NOT update canonical atoms — caller must handle that.
sp_set_index(SpaceAtom, NewIndex, ok) :-
    ffi_inc(sp_set_index),
    sp_set_space_index(SpaceAtom, NewIndex).

%% sp_delete(+SpaceAtom, -Ok)
%% Delete a MapSpace or SetSpace, freeing sp_type/sp_index facts.
sp_delete(SpaceAtom, ok) :-
    ffi_inc(sp_delete),
    forall(
        current_predicate(SpaceAtom/Arity),
        abolish(SpaceAtom/Arity)
    ),
    ( sp_index_key(SpaceAtom, Key)
    -> ( catch(nb_delete(Key), _, true),
         retractall(sp_index_key(SpaceAtom, _)) )
    ;  true
    ),
    retractall(sp_index(SpaceAtom, _)),
    retractall(sp_type(SpaceAtom, _)),
    retractall(sp_mode(SpaceAtom, _)).

%% ======================================================================
%% Normal PeTTa space API integration (multifile hooks)
%% ======================================================================

:- multifile match/4.
:- multifile 'add-atom'/3.
:- multifile 'remove-atom'/3.
:- multifile 'get-atoms'/2.

'add-atom'(Space, [kv, Key, Value], true) :-
    sp_type(Space, map), !,
    sp_map_put(Space, Key, Value, _).

'add-atom'(Space, [member, Elem], true) :-
    sp_type(Space, set), !,
    sp_set_add(Space, Elem, _).

match(Space, [kv, Key, Value], OutPattern, Result) :-
    sp_type(Space, map), !,
    sp_get_space_index(Space, Assoc),
    ( nonvar(Key)
    -> get_assoc(Key, Assoc, Value)
    ;  assoc_pair(Assoc, Key, Value)
    ),
    Result = OutPattern.

match(Space, [member, Elem], OutPattern, Result) :-
    sp_type(Space, set), !,
    sp_get_space_index(Space, Set),
    ( nonvar(Elem)
    -> ord_memberchk(Elem, Set)
    ;  member(Elem, Set)
    ),
    Result = OutPattern.

'get-atoms'(Space, [kv, Key, Value]) :-
    sp_type(Space, map), !,
    sp_get_space_index(Space, Assoc),
    assoc_pair(Assoc, Key, Value).

'get-atoms'(Space, [member, Elem]) :-
    sp_type(Space, set), !,
    sp_get_space_index(Space, Set),
    member(Elem, Set).

'remove-atom'(Space, [kv, Key, _], true) :-
    sp_type(Space, map), !,
    sp_map_del(Space, Key, _).

'remove-atom'(Space, [member, Elem], true) :-
    sp_type(Space, set), !,
    sp_set_del(Space, Elem, _).

%% Helper: enumerate key-value pairs from an assoc
assoc_pair(Assoc, Key, Value) :-
    assoc_to_keys(Assoc, Keys),
    member(Key, Keys),
    get_assoc(Key, Assoc, Value).

%% ============================================================================
%% Job TSV parsing
%% ============================================================================
%%
%% Jobs TSV format:
%%   job<TAB>job_id<TAB>data_tsv<TAB>query_tsv
%%
%% Returns rows as:
%%   [JobId, DataPath, QueryPath]

zar_jobs_parse_jobs_file(Filename, Rows) :-
    read_lines(Filename, Lines),
    zar_jobs_parse_job_lines(Lines, Rows).

zar_jobs_parse_job_lines([], []).
zar_jobs_parse_job_lines([Line|Rest], Rows) :-
    ( zar_jobs_skip_line(Line)
    -> zar_jobs_parse_job_lines(Rest, Rows)
    ; ( zar_jobs_parse_job_line(Line, Row)
      -> Rows = [Row|Tail],
         zar_jobs_parse_job_lines(Rest, Tail)
      ;  zar_jobs_parse_job_lines(Rest, Rows)
      )
    ).

zar_jobs_skip_line(Line) :-
    skip_line(Line).

%% Alias for consistency with zar_io_* naming.
zar_io_parse_jobs_file(Filename, Rows) :-
    zar_jobs_parse_jobs_file(Filename, Rows).
is_parse_jobs_file(Filename, Rows) :-
    zar_jobs_parse_jobs_file(Filename, Rows).
parse_jobs_file(Filename, Rows) :-
    zar_jobs_parse_jobs_file(Filename, Rows).

zar_jobs_parse_job_line(Line, [JobId, DataPath, QueryPath]) :-
    split_string(Line, "\t", " \t\r", [TagS, JobS, DataS, QueryS]),
    string_lower(TagS, "job"),
    atom_string(JobId, JobS),
    atom_string(DataPath, DataS),
    atom_string(QueryPath, QueryS).

%% ============================================================================
%% Math kernels
%% ============================================================================
%%
%% Stable numerics for log-domain scoring and confidence projections.
%% Naming kept short and generic by design.

safe_ln(X, -690.0) :-
    X =< 0.0, !.
safe_ln(X, Ln) :-
    Ln is log(X).

gate_from_mass(Mass, GateKappa, Gate) :-
    ( Mass =< 0.0
    -> Gate = 0.0
    ;  K2 is max(GateKappa, 1.0e-9),
       Gate is Mass / (Mass + K2)
    ).

sigmoid_diff(D, S) :-
    ( D >= 0.0
    -> Z is exp(-D),
       S is 1.0 / (1.0 + Z)
    ;  Z is exp(D),
       S is Z / (1.0 + Z)
    ).

zar_internal_logsumexp2(A, B, R) :-
    ( A >= B
    -> R is A + log(1.0 + exp(B - A))
    ;  R is B + log(1.0 + exp(A - B))
    ).

evidence_to_stv(Pos, Neg, Kappa, Strength, Confidence) :-
    Total is Pos + Neg,
    ( Total =:= 0.0
    -> Strength = 0.0,
       Confidence = 0.0
    ;  Strength is Pos / Total,
       K2 is max(Kappa, 1.0e-12),
       Confidence is Total / (Total + K2)
    ).

stv_from_logs(LogPos, LogNeg, Kappa, Strength, Confidence) :-
    Diff is LogPos - LogNeg,
    sigmoid_diff(Diff, Strength),
    zar_internal_logsumexp2(LogPos, LogNeg, LogTotal),
    K2 is max(Kappa, 1.0e-12),
    safe_ln(K2, LogKappa),
    Delta is LogTotal - LogKappa,
    sigmoid_diff(Delta, Confidence).

posterior_from_prior_and_like(PriorPos, PriorNeg, LikeLogPos, LikeLogNeg, Kappa, Strength, Confidence) :-
    safe_ln(PriorPos, PriorLogPos),
    safe_ln(PriorNeg, PriorLogNeg),
    LogPos is PriorLogPos + LikeLogPos,
    LogNeg is PriorLogNeg + LikeLogNeg,
    stv_from_logs(LogPos, LogNeg, Kappa, Strength, Confidence).

%% Compatibility aliases (legacy call sites)
zar_math_safe_ln(A, B) :-
    safe_ln(A, B).
zar_math_gate_from_mass(A, B, C) :-
    gate_from_mass(A, B, C).
zar_math_sigmoid_diff(A, B) :-
    sigmoid_diff(A, B).
zar_math_logsumexp2(A, B, C) :-
    zar_internal_logsumexp2(A, B, C).
zar_math_evidence_to_stv(A, B, C, D, E) :-
    evidence_to_stv(A, B, C, D, E).
zar_math_stv_from_logs(A, B, C, D, E) :-
    stv_from_logs(A, B, C, D, E).
zar_math_posterior_from_prior_and_like(A, B, C, D, E, F, G) :-
    posterior_from_prior_and_like(A, B, C, D, E, F, G).

%% ======================================================================
%% Logistic Regression Batch Helpers
%% ======================================================================

zar_logistic_site_evidence_batch(Features, Kappas, Omegas, Partials, [WeightSum, WeightedSum, WeightedSumSq]) :-
    ffi_inc(zar_logistic_site_evidence_batch),
    zar_logistic_site_evidence_batch_(Features, Kappas, Omegas, Partials, 0.0, 0.0, 0.0, WeightSum, WeightedSum, WeightedSumSq).

zar_logistic_site_evidence_batch_([], [], [], [], W, S, SS, W, S, SS).
zar_logistic_site_evidence_batch_([Feature|Features], [Kappa|Kappas], [Omega|Omegas], [Partial|Partials], W0, S0, SS0, W, S, SS) :-
    Precision is Omega * Feature * Feature,
    ( Precision =< 1.0e-9 ->
        PseudoObservation = 0.0
    ;   Linear is Feature * (Kappa - Omega * Partial),
        PseudoObservation is Linear / Precision
    ),
    W1 is W0 + Precision,
    S1 is S0 + Precision * PseudoObservation,
    SS1 is SS0 + Precision * PseudoObservation * PseudoObservation,
    zar_logistic_site_evidence_batch_(Features, Kappas, Omegas, Partials, W1, S1, SS1, W, S, SS).

zar_logistic_site_xi(Eta, Variance, Xi) :-
    VarianceSafe is max(0.0, Variance),
    Xi is sqrt(Eta * Eta + VarianceSafe).

zar_logistic_site_weight(Xi, Omega) :-
    XiSafe is max(Xi, 1.0e-6),
    ( XiSafe =< 1.0e-6
    -> Omega = 0.25
    ;  Omega is tanh(XiSafe / 2.0) / (2.0 * XiSafe)
    ).

zar_logistic_site_hyper_batch_flat(Etas, Variances, FlatPairs) :-
    ffi_inc(zar_logistic_site_hyper_batch_flat),
    zar_logistic_site_hyper_batch_flat_(Etas, Variances, FlatPairs).

zar_logistic_site_hyper_batch_flat_([], [], []).
zar_logistic_site_hyper_batch_flat_([Eta|Etas], [Variance|Variances], [Xi, Omega|FlatPairs]) :-
    zar_logistic_site_xi(Eta, Variance, Xi),
    zar_logistic_site_weight(Xi, Omega),
    zar_logistic_site_hyper_batch_flat_(Etas, Variances, FlatPairs).

zar_logistic_posterior_params_batch_flat(PriorMeans, PriorPrecisions, EvidenceFlat, FlatPosterior) :-
    ffi_inc(zar_logistic_posterior_params_batch_flat),
    zar_logistic_posterior_params_batch_flat_(PriorMeans, PriorPrecisions, EvidenceFlat, FlatPosterior).

zar_logistic_posterior_params_batch_flat_([], [], [], []).
zar_logistic_posterior_params_batch_flat_([PriorMean|PriorMeans], [PriorPrecision|PriorPrecisions], [WeightSum, WeightedSum, _WeightedSumSq|EvidenceFlat], [PosteriorMean, PosteriorPrecision|FlatPosterior]) :-
    PosteriorPrecision is PriorPrecision + WeightSum,
    PosteriorMean is (PriorPrecision * PriorMean + WeightedSum) / PosteriorPrecision,
    zar_logistic_posterior_params_batch_flat_(PriorMeans, PriorPrecisions, EvidenceFlat, FlatPosterior).
