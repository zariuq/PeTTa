:- ensure_loaded(metta).

prologfunc(X,Y) :- Y is X+1.

prolog_interop_example :- register_fun(prologfunc),
                          process_metta_string("(= (mettafunc $x) (prologfunc $x))", _),
                          listing(mettafunc),
                          mettafunc(30, R),
                          format("mettafunc(30) = ~w~n", [R]).

runtime_arg('--he').
runtime_arg('--silent').
runtime_arg('-s').
runtime_arg(silent).
runtime_arg(mork).

strip_runtime_args([], []).
strip_runtime_args([Arg | Rest], Out) :-
    runtime_arg(Arg), !,
    strip_runtime_args(Rest, Out).
strip_runtime_args([Arg | Rest], [Arg | Out]) :-
    strip_runtime_args(Rest, Out).

main :- current_prolog_flag(argv, Args),
        set_metta_profile_from_args(Args),
        ( Args = [] -> prolog_interop_example
        ; Args = [mork] -> prolog_interop_example,
                           mork_test
        ; strip_runtime_args(Args, [File|_]) -> file_directory_name(File, Dir),
                                                assertz(working_dir(Dir)),
                                                load_metta_file(File,Results),
                                                maplist(swrite,Results,ResultsR),
                                                maplist(format("~w~n"), ResultsR)
        ),
        halt.

:- initialization(main, main).
