% Default all stream I/O to UTF-8.
%
% MeTTa source files are UTF-8 by convention, but SWI-Prolog derives its
% default `encoding` flag from the ambient locale. Where that locale is not
% UTF-8 - Windows (cp1252), or any POSIX/C locale, which minimal container
% images and CI runners commonly have - read_file_to_string/3 in
% filereader.pl decodes .metta sources in the locale codepage instead, and
% multi-byte characters in string literals or symbol names silently become
% several wrong characters.
%
% Setting the flag here, before anything opens a stream, makes source loading
% deterministic regardless of environment. It is a no-op where the locale is
% already UTF-8.
:- set_prolog_flag(encoding, utf8).

:- ensure_loaded(metta).
:- multifile prolog:error_message//1.

% Type error messages (see types.pl); examples/fail_*.metta expect them.
% Values and types print as MeTTa, a rigid type variable as $1, $2, ...:
prolog:error_message(literal_type_mismatch(Value, Required)) -->
    { metta_text(Value, V), metta_text(Required, R) },
    [ 'Type mismatch: got ~w but expected ~w'-[V, R] ].
prolog:error_message(type_conflict(existing(Existing), required(Required))) -->
    { metta_text(Existing, E), metta_text(Required, R) },
    [ 'Type conflict: value is constrained as ~w but also required as ~w'-[E, R] ].
prolog:error_message(no_matching_overload(Fun)) -->
    [ 'No matching typed overload for ~w'-[Fun] ].
metta_text(T, S) :- copy_term_nat(T, C), mapsubterms([X, A]>>( compound(X), X = '$rigid'(I), format(atom(A), '$~w', [I]) ), C, D),
                    swrite(D, S).

is_silent_flag(silent).
is_silent_flag('--silent').
is_silent_flag('-s').

strip_silent_flags([], []).
strip_silent_flags([Arg|Rest], Filtered) :-
        is_silent_flag(Arg),
        !,
        strip_silent_flags(Rest, Filtered).
strip_silent_flags([Arg|Rest], [Arg|Filtered]) :-
        strip_silent_flags(Rest, Filtered).

prologfunc(X,Y) :- Y is X+1.

prolog_interop_example :- register_fun(prologfunc),
                          process_metta_string("(= (mettafunc $x) (prologfunc $x))", _),
                          listing(mettafunc),
                          mettafunc(30, R),
                          format("mettafunc(30) = ~w~n", [R]).

main :- current_prolog_flag(argv, RawArgs),
        strip_silent_flags(RawArgs, Args),
        ( Args = [] -> prolog_interop_example
        ; Args = [mork] -> prolog_interop_example,
                           mork_test
        ; metta_files(Args, Files), Files = [First|_]
          -> file_directory_name(First, Dir),
             assertz(working_dir(Dir)),
             maplist(load_metta_file, Files, ResultsList),
             append(ResultsList, Results),
             maplist(swrite,Results,ResultsR),
             maplist(format("~w~n"), ResultsR)
        ),
        ( metta_runnable_error -> halt(2) ; halt ).

% Several .metta files may be named, and they are loaded in exactly the order
% given. Leading arguments ending in .metta are files; everything from the
% first non-file argument on is flags.
% Without a leading .metta argument the first argument is the one file to load,
% whatever its extension, as before several files could be named.
metta_files(Args, Files) :- leading_metta_files(Args, Files), Files = [_|_], !.
metta_files([File|_], [File]).

leading_metta_files([A|As], [A|Fs]) :- atom(A), file_name_extension(_, metta, A), !,
                                       leading_metta_files(As, Fs).
leading_metta_files(_, []).

:- initialization(main, main).
