:- dynamic silent/1.
:- dynamic working_dir/1.

set_silent(true) :-
    retractall(silent(_)),
    assertz(silent(false)),
    !.
set_silent(false) :-
    retractall(silent(_)),
    assertz(silent(true)).

set_working_dir(load_metta_file, File) :-
    file_directory_name(File, Dir),
    retractall(working_dir(_)),
    assertz(working_dir(Dir)),
    !.
set_working_dir(_, _).

run_metta_helper(Verbose, Predicate, Arg, ResultsR) :-
    set_silent(Verbose),
    set_working_dir(Predicate, Arg),
    call(Predicate, Arg, Results),
    maplist(swrite,Results,ResultsR).
