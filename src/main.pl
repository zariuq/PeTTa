:- ensure_loaded(metta).

:- dynamic cmdline_args/1.
:- assert(cmdline_args([])).

prologfunc(X,Y) :- Y is X+1.

% ---------------------------------------------------------------------------
% Command-line argument access (pverify/mmverify-compatible)
% ---------------------------------------------------------------------------

% get_cmdline_arg(+Index, -Arg) - Get argument by 0-based index
% Returns 'Empty' if index is out of bounds.
get_cmdline_arg(Index, Arg) :-
    cmdline_args(Args),
    ( nth0(Index, Args, A)
    -> Arg = A
    ;  Arg = 'Empty'
    ).

% get_cmdline_args(-Args) - Get all user command-line arguments.
get_cmdline_args(Args) :-
    cmdline_args(Args).

% cmdline_arg_count(-Count) - Number of user command-line arguments.
cmdline_arg_count(Count) :-
    cmdline_args(Args),
    length(Args, Count).

% has_cmdline_args(-Bool) - true iff there is at least one user arg.
has_cmdline_args(true) :-
    cmdline_args(Args),
    Args \= [],
    !.
has_cmdline_args(false).

% Filter out internal flags from argument list.
filter_internal_args([], []).
filter_internal_args([Arg|Rest], Filtered) :-
    ( Arg == '--silent'
    ; Arg == mork
    ),
    !,
    filter_internal_args(Rest, Filtered).
filter_internal_args([Arg|Rest], [Arg|RestFiltered]) :-
    filter_internal_args(Rest, RestFiltered).

prolog_interop_example :- register_fun(prologfunc),
                          process_metta_string("(= (mettafunc $x) (prologfunc $x))", _),
                          listing(mettafunc),
                          mettafunc(30, R),
                          format("mettafunc(30) = ~w~n", [R]).

main :- current_prolog_flag(argv, Args),
        ( Args = [] -> prolog_interop_example
        ; Args = [mork] -> prolog_interop_example,
                           mork_test
        ; Args = [File|RestArgs] ->
                             filter_internal_args(RestArgs, UserArgs),
                             retractall(cmdline_args(_)),
                             assert(cmdline_args(UserArgs)),
                             file_directory_name(File, Dir),
                             assertz(working_dir(Dir)),
                             load_metta_file(File,Results),
                             maplist(swrite,Results,ResultsR),
                             maplist(format("~w~n"), ResultsR)
        ),
        halt.

:- initialization(main, main).
