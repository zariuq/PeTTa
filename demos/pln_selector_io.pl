%% pln_selector_io.pl - unified IO layer for PLN selector demos
%%
%% One shared file to reduce duplication across:
%%   - pln_premise_io.pl
%%   - pln_normal_io.pl
%%   - pln_enhanced_io.pl
%%   - pln_knn_io.pl
%%   - pln_jobs_io.pl

:- ['../lib/lib_zar.pl'].
:- use_module(library(aggregate)).

%% ---------------------------------------------------------------------------
%% Shared helpers
%% ---------------------------------------------------------------------------
%%
%% get_cmdline_arg/2 and related command-line predicates are imported from
%% ../lib/lib_import.pl via lib_import.metta (pverify/mmverify-compatible API).

%% NOTE:
%% keep old selector-facing names while delegating to shared helpers.
shared_read_lines(Filename, Lines) :-
    read_lines(Filename, Lines).

shared_to_atoms(In, Out) :-
    to_atoms(In, Out).

shared_to_numbers(In, Out) :-
    to_numbers(In, Out).

%% ---------------------------------------------------------------------------
%% Premise/NB IO
%% ---------------------------------------------------------------------------

:- dynamic nb_prior_db/3.
:- dynamic nb_feat_db/5.
:- dynamic nb_param_db/2.

parse_nb_evidence_file(Filename, Rows) :-
    shared_read_lines(Filename, Lines),
    parse_evidence_lines(Lines, Rows).

parse_nb_queries_file(Filename, Rows) :-
    shared_read_lines(Filename, Lines),
    parse_query_lines(Lines, Rows).

clear_nb_evidence_db :-
    retractall(nb_prior_db(_, _, _)),
    retractall(nb_feat_db(_, _, _, _, _)),
    retractall(nb_param_db(_, _)).

load_nb_evidence_db(Filename, true) :-
    clear_nb_evidence_db,
    parse_nb_evidence_file(Filename, Rows),
    assert_nb_evidence_rows(Rows).

assert_nb_evidence_rows([]).
assert_nb_evidence_rows([Row|Rest]) :-
    assert_nb_evidence_row(Row),
    assert_nb_evidence_rows(Rest).

assert_nb_evidence_row([prior, Axiom, Pos, Neg]) :-
    !,
    assertz(nb_prior_db(Axiom, Pos, Neg)).
assert_nb_evidence_row([feat, Axiom, Feature, Pos, Neg, Idf]) :-
    !,
    assertz(nb_feat_db(Axiom, Feature, Pos, Neg, Idf)).
assert_nb_evidence_row([param, Name, Value]) :-
    !,
    assertz(nb_param_db(Name, Value)).
assert_nb_evidence_row(_).

lookup_prior_db(Axiom, Pair) :-
    ( nb_prior_db(Axiom, Pos, Neg)
    -> Pair = [Pos, Neg]
    ;  Pair = []
    ).

lookup_feature_db(Axiom, Feature, Pair) :-
    ( nb_feat_db(Axiom, Feature, Pos, Neg, _)
    -> Pair = [Pos, Neg]
    ;  Pair = []
    ).

lookup_feature_idf_db(Axiom, Feature, Triple) :-
    ( nb_feat_db(Axiom, Feature, Pos, Neg, Idf)
    -> Triple = [Pos, Neg, Idf]
    ;  Triple = []
    ).

lookup_param_db(Name, Value) :-
    ( param_db(Name, V)
    -> Value = V
    ; nb_param_db(Name, V2)
    -> Value = V2
    ;  Value = []
    ).

parse_evidence_lines([], []).
parse_evidence_lines([Line|Rest], Rows) :-
    ( skip_line(Line)
    -> parse_evidence_lines(Rest, Rows)
    ; ( parse_evidence_line(Line, Row)
      -> Rows = [Row|Tail],
         parse_evidence_lines(Rest, Tail)
      ;  parse_evidence_lines(Rest, Rows)
      )
    ).

parse_query_lines([], []).
parse_query_lines([Line|Rest], Rows) :-
    ( skip_line(Line)
    -> parse_query_lines(Rest, Rows)
    ; ( parse_query_line(Line, Row)
      -> Rows = [Row|Tail],
         parse_query_lines(Rest, Tail)
      ;  parse_query_lines(Rest, Rows)
      )
    ).

parse_evidence_line(Line, Row) :-
    split_string(Line, "\t", " \t\r", Parts),
    ( Parts = [TagS, NameS, ValueS],
      string_lower(TagS, "param"),
      number_string(Value, ValueS),
      atom_string(Name, NameS),
      Row = [param, Name, Value]
    ; Parts = [TagS, AxiomS, PosS, NegS],
      string_lower(TagS, "prior"),
      number_string(Pos, PosS),
      number_string(Neg, NegS),
      atom_string(Axiom, AxiomS),
      Row = [prior, Axiom, Pos, Neg]
    ; Parts = [TagS, AxiomS, FeatureS, PosS, NegS],
      string_lower(TagS, "feat"),
      number_string(Pos, PosS),
      number_string(Neg, NegS),
      atom_string(Axiom, AxiomS),
      atom_string(Feature, FeatureS),
      Row = [feat, Axiom, Feature, Pos, Neg, 1.0]
    ; Parts = [TagS, AxiomS, FeatureS, PosS, NegS, IdfS],
      string_lower(TagS, "feat"),
      number_string(Pos, PosS),
      number_string(Neg, NegS),
      number_string(Idf, IdfS),
      atom_string(Axiom, AxiomS),
      atom_string(Feature, FeatureS),
      Row = [feat, Axiom, Feature, Pos, Neg, Idf]
    ).

%% query_id<TAB>axiom<TAB>features
parse_query_line(Line, [QueryId, Axiom, Features]) :-
    split_string(Line, "\t", " \t\r", [QueryIdS, AxiomS, FeatureCsv]),
    atom_string(QueryId, QueryIdS),
    atom_string(Axiom, AxiomS),
    split_string(FeatureCsv, ",", " \t\r", FeatureStrs),
    shared_to_atoms(FeatureStrs, Features).

%% query_id<TAB>axiom<TAB>features<TAB>strengths
parse_query_line(Line, [QueryId, Axiom, Features, Strengths]) :-
    split_string(Line, "\t", " \t\r", [QueryIdS, AxiomS, FeatureCsv, StrengthCsv]),
    atom_string(QueryId, QueryIdS),
    atom_string(Axiom, AxiomS),
    split_string(FeatureCsv, ",", " \t\r", FeatureStrs),
    split_string(StrengthCsv, ",", " \t\r", StrengthStrs),
    shared_to_atoms(FeatureStrs, Features),
    shared_to_numbers(StrengthStrs, Strengths).

%% ---------------------------------------------------------------------------
%% Normal-Normal IO
%% ---------------------------------------------------------------------------

:- dynamic normal_obs_db/3.
:- dynamic normal_param_db/2.

clear_normal_db :-
    retractall(normal_obs_db(_, _, _)),
    retractall(normal_param_db(_, _)).

load_normal_db(Filename, true) :-
    clear_normal_db,
    shared_read_lines(Filename, Lines),
    parse_normal_lines(Lines).

parse_normal_lines([]).
parse_normal_lines([Line|Rest]) :-
    ( skip_line(Line)
    -> parse_normal_lines(Rest)
    ; ( parse_normal_line(Line)
      -> parse_normal_lines(Rest)
      ;  parse_normal_lines(Rest)
      )
    ).

parse_normal_line(Line) :-
    split_string(Line, "\t", " \t\r", Parts),
    parse_normal_parts(Parts).

parse_normal_parts([TagS, AxiomS, XS, NS]) :-
    string_lower(TagS, "obs"),
    !,
    number_string(X, XS),
    number_string(N, NS),
    atom_string(Axiom, AxiomS),
    assertz(normal_obs_db(Axiom, X, N)).

parse_normal_parts([TagS, NameS, ValueS]) :-
    string_lower(TagS, "param"),
    !,
    number_string(Value, ValueS),
    atom_string(Name, NameS),
    assertz(normal_param_db(Name, Value)).

parse_normal_parts(_).

lookup_normal_obs_db(Axiom, Triple) :-
    ( normal_obs_db(Axiom, X, N)
    -> Triple = [X, N]
    ;  Triple = []
    ).

lookup_normal_param_db(Name, Value) :-
    ( normal_param_db(Name, V)
    -> Value = V
    ;  Value = []
    ).

parse_normal_queries_file(Filename, Rows) :-
    parse_axiom_queries_file(Filename, Rows).

%% ---------------------------------------------------------------------------
%% Enhanced IO
%% ---------------------------------------------------------------------------

:- dynamic init_stv_db/3.
:- dynamic cooc_idf_db/5.
:- dynamic param_db/2.

clear_enhanced_db :-
    retractall(init_stv_db(_, _, _)),
    retractall(cooc_idf_db(_, _, _, _, _)),
    retractall(param_db(_, _)).

load_enhanced_db(Filename, true) :-
    clear_enhanced_db,
    shared_read_lines(Filename, Lines),
    parse_enhanced_lines(Lines).

parse_enhanced_lines([]).
parse_enhanced_lines([Line|Rest]) :-
    ( skip_line(Line)
    -> parse_enhanced_lines(Rest)
    ; ( parse_enhanced_line(Line)
      -> parse_enhanced_lines(Rest)
      ;  parse_enhanced_lines(Rest)
      )
    ).

parse_enhanced_line(Line) :-
    split_string(Line, "\t", " \t\r", Parts),
    parse_enhanced_parts(Parts).

parse_enhanced_parts([TagS, AxiomS, StrS, ConfS]) :-
    string_lower(TagS, "init"),
    !,
    number_string(Str, StrS),
    number_string(Conf, ConfS),
    atom_string(Axiom, AxiomS),
    assertz(init_stv_db(Axiom, Str, Conf)).

parse_enhanced_parts([TagS, AxiomAS, AxiomBS, PosS, NegS, IdfS]) :-
    string_lower(TagS, "cooc"),
    !,
    number_string(Pos, PosS),
    number_string(Neg, NegS),
    number_string(Idf, IdfS),
    atom_string(AxiomA, AxiomAS),
    atom_string(AxiomB, AxiomBS),
    assertz(cooc_idf_db(AxiomA, AxiomB, Pos, Neg, Idf)),
    assertz(cooc_idf_db(AxiomB, AxiomA, Pos, Neg, Idf)).

parse_enhanced_parts([TagS, NameS, ValueS]) :-
    string_lower(TagS, "param"),
    !,
    number_string(Value, ValueS),
    atom_string(Name, NameS),
    assertz(param_db(Name, Value)).

parse_enhanced_parts(_).

lookup_init_stv_db(Axiom, Pair) :-
    ( init_stv_db(Axiom, S, C)
    -> Pair = [S, C]
    ;  Pair = []
    ).

lookup_cooc_partners_idf_db(Axiom, Partners) :-
    findall([Partner, Pos, Neg, Idf],
            (cooc_idf_db(Axiom, Partner, Pos, Neg, Idf),
             init_stv_db(Partner, _, _)),
            Partners).

parse_enhanced_queries_file(Filename, Rows) :-
    parse_axiom_queries_file(Filename, Rows).

%% ---------------------------------------------------------------------------
%% kNN + NB combined IO
%% ---------------------------------------------------------------------------

:- dynamic goal_feat_db/1.
:- dynamic nbr_feat_db/2.
:- dynamic nbr_used_db/2.
:- dynamic nbr_list_db/1.

clear_all_db :-
    retractall(goal_feat_db(_)),
    retractall(nbr_feat_db(_, _)),
    retractall(nbr_used_db(_, _)),
    retractall(nb_prior_db(_, _, _)),
    retractall(nb_feat_db(_, _, _, _, _)),
    retractall(param_db(_, _)),
    retractall(nbr_list_db(_)).

load_nb_from_pl(Filename, true) :-
    retractall(nb_prior_db(_, _, _)),
    retractall(nb_feat_db(_, _, _, _, _)),
    ( string(Filename)
    -> atom_string(FileAtom, Filename)
    ;  FileAtom = Filename
    ),
    consult(FileAtom).

load_combined_db(Filename, true) :-
    clear_all_db,
    shared_read_lines(Filename, Lines),
    parse_all_lines(Lines),
    build_nbr_list.

parse_all_lines([]).
parse_all_lines([Line|Rest]) :-
    ( skip_line(Line) -> true ; parse_combined_parts(Line) ),
    parse_all_lines(Rest).

parse_combined_parts(Line) :-
    split_string(Line, "\t", " \t\r", Parts),
    parse_combined_fields(Parts), !.
parse_combined_parts(_).

parse_combined_fields([TagS, FeatS]) :-
    string_lower(TagS, "goal_feat"),
    atom_string(Feat, FeatS),
    assertz(goal_feat_db(Feat)).

parse_combined_fields([TagS, NbrS, FeatS]) :-
    string_lower(TagS, "nbr_feat"),
    atom_string(Nbr, NbrS),
    atom_string(Feat, FeatS),
    assertz(nbr_feat_db(Nbr, Feat)).

parse_combined_fields([TagS, NbrS, AxiomS]) :-
    string_lower(TagS, "nbr_used"),
    atom_string(Nbr, NbrS),
    atom_string(Axiom, AxiomS),
    assertz(nbr_used_db(Nbr, Axiom)).

parse_combined_fields([TagS, AxiomS, PosS, NegS]) :-
    string_lower(TagS, "prior"),
    atom_string(Axiom, AxiomS),
    number_string(Pos, PosS),
    number_string(Neg, NegS),
    assertz(nb_prior_db(Axiom, Pos, Neg)).

parse_combined_fields([TagS, AxiomS, FeatS, PosS, NegS]) :-
    string_lower(TagS, "feat"),
    atom_string(Axiom, AxiomS),
    atom_string(Feat, FeatS),
    number_string(Pos, PosS),
    number_string(Neg, NegS),
    assertz(nb_feat_db(Axiom, Feat, Pos, Neg, 1.0)).

parse_combined_fields([TagS, AxiomS, FeatS, PosS, NegS, IdfS]) :-
    string_lower(TagS, "feat"),
    atom_string(Axiom, AxiomS),
    atom_string(Feat, FeatS),
    number_string(Pos, PosS),
    number_string(Neg, NegS),
    number_string(Idf, IdfS),
    assertz(nb_feat_db(Axiom, Feat, Pos, Neg, Idf)).

parse_combined_fields([TagS, NameS, ValueS]) :-
    string_lower(TagS, "param"),
    string_lower(NameS, "nb_pl_file"),
    !,
    atom_string(Value, ValueS),
    assertz(param_db(nb_pl_file, Value)).

parse_combined_fields([TagS, NameS, ValueS]) :-
    string_lower(TagS, "param"),
    atom_string(Name, NameS),
    number_string(Value, ValueS),
    assertz(param_db(Name, Value)).

parse_combined_fields(_).

build_nbr_list :-
    findall(N, nbr_feat_db(N, _), NsRaw),
    sort(NsRaw, Ns),
    assert_nbr_list(Ns).

assert_nbr_list([]).
assert_nbr_list([N|Rest]) :-
    assertz(nbr_list_db(N)),
    assert_nbr_list(Rest).

compute_overlap(Neighbor, Result) :-
    aggregate_all(count, (goal_feat_db(F), nbr_feat_db(Neighbor, F)), Shared),
    ( Shared =:= 0
    -> Result = []
    ;  aggregate_all(count, goal_feat_db(_), LenG),
       aggregate_all(count, nbr_feat_db(Neighbor, _), LenN),
       Diff is LenG + LenN - 2 * Shared,
       Result = [Shared, Diff]
    ).

check_nbr_used(Neighbor, Axiom, Result) :-
    ( nbr_used_db(Neighbor, Axiom)
    -> Result = 1
    ;  Result = 0
    ).

get_all_neighbors(Neighbors) :-
    findall(N, nbr_list_db(N), Neighbors).

get_axiom_neighbor_evidence(Axiom, Rows) :-
    findall([Neighbor, Shared, Diff, Used],
            ( nbr_list_db(Neighbor),
              compute_overlap(Neighbor, OvResult),
              OvResult = [Shared, Diff],
              check_nbr_used(Neighbor, Axiom, Used)
            ),
            Rows).

parse_combined_queries_file(Filename, Rows) :-
    shared_read_lines(Filename, Lines),
    parse_combined_query_lines(Lines, Rows).

parse_combined_query_lines([], []).
parse_combined_query_lines([Line|Rest], Rows) :-
    ( skip_line(Line)
    -> parse_combined_query_lines(Rest, Rows)
    ; ( parse_combined_query_line(Line, Row)
      -> Rows = [Row|Tail], parse_combined_query_lines(Rest, Tail)
      ;  parse_combined_query_lines(Rest, Rows)
      )
    ).

parse_combined_query_line(Line, [QueryId, Axiom, Features]) :-
    split_string(Line, "\t", " \t\r", [_TagS, QidS, AxiomS, FeatCsv]),
    atom_string(QueryId, QidS),
    atom_string(Axiom, AxiomS),
    split_string(FeatCsv, ",", " \t\r", FeatStrs),
    shared_to_atoms(FeatStrs, Features).

parse_combined_query_line(Line, [QueryId, Axiom, []]) :-
    split_string(Line, "\t", " \t\r", [_TagS, QidS, AxiomS]),
    atom_string(QueryId, QidS),
    atom_string(Axiom, AxiomS).
