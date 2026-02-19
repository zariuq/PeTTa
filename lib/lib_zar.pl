%% lib_zar.pl - shared Prolog helpers for PeTTa demos
%%
%% Consolidated utilities:
%%   - job TSV parsing (used by batched selectors)
%%   - numerically stable math kernels (used by PLN scoring hot paths)
%%
%% Intentionally non-module style so existing `(consult)` + `import_prolog_function`
%% flows can import predicates directly without module qualification.

:- use_module(library(readutil)).

%% ============================================================================
%% Shared IO helpers
%% ============================================================================

%% 0-based CLI arg access helper.
%% Index 0 is the first user arg after the script path.
%% Mirrors pverify/mmverify filtering of internal flags.
get_cmdline(Index, Arg) :-
    current_prolog_flag(argv, RawArgs),
    ( RawArgs = [_Script|Rest]
    -> UserRaw = Rest
    ;  UserRaw = []
    ),
    get_cmdline_filter_internal(UserRaw, UserArgs),
    ( nth0(Index, UserArgs, A)
    -> Arg = A
    ;  Arg = 'Empty'
    ).

get_cmdline_filter_internal([], []).
get_cmdline_filter_internal([Arg|Rest], Filtered) :-
    ( Arg == '--silent'
    ; Arg == mork
    ),
    !,
    get_cmdline_filter_internal(Rest, Filtered).
get_cmdline_filter_internal([Arg|Rest], [Arg|Tail]) :-
    get_cmdline_filter_internal(Rest, Tail).

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
    get_cmdline(Index, Arg).
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
    get_cmdline(Index, Arg).
zar_skip_line(Line) :-
    skip_line(Line).
zar_io_get_cmdline_arg(Index, Arg) :-
    get_cmdline(Index, Arg).
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
