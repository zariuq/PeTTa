%% cnf_parser.pl - DIMACS CNF parser for PeTTa
%%
%% Parses DIMACS CNF files into MeTTa clause format
%% Usage: parse_cnf_file(+Filename, -Clauses)

:- use_module(library(readutil)).

%% parse_cnf_file(+Filename, -Clauses)
%% Reads a DIMACS CNF file and returns clauses as nested lists
parse_cnf_file(Filename, Clauses) :-
    read_file_to_string(Filename, Content, []),
    split_string(Content, "\n", "", Lines),
    parse_lines(Lines, Clauses).

%% parse_lines(+Lines, -Clauses)
parse_lines([], []).
parse_lines([Line|Rest], Clauses) :-
    string_chars(Line, Chars),
    ( Chars = [] -> parse_lines(Rest, Clauses)  % empty line
    ; Chars = ['c'|_] -> parse_lines(Rest, Clauses)  % comment
    ; Chars = ['p'|_] -> parse_lines(Rest, Clauses)  % header
    ; Chars = ['%'|_] -> parse_lines(Rest, Clauses)  % comment
    ; parse_clause_line(Line, Lits),
      ( Lits = [] -> parse_lines(Rest, Clauses)
      ; Clauses = [Lits|MoreClauses],
        parse_lines(Rest, MoreClauses)
      )
    ).

%% parse_clause_line(+Line, -Lits)
%% Parse a line of integers ending in 0
parse_clause_line(Line, Lits) :-
    split_string(Line, " \t", " \t", Parts),
    parse_ints(Parts, Lits).

parse_ints([], []).
parse_ints([S|Rest], Lits) :-
    ( S = "" -> parse_ints(Rest, Lits)
    ; number_string(N, S),
      ( N =:= 0 -> Lits = []
      ; int_to_lit(N, Lit),
        Lits = [Lit|MoreLits],
        parse_ints(Rest, MoreLits)
      )
    ).

%% int_to_lit(+Int, -Lit)
%% Return just the integer - let MeTTa decide positive/negative
int_to_lit(N, N).
