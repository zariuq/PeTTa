%Hooks for extensions (lib_memo, lib_det). Every clause of an event hook runs
%(callers use forall/2), so each extension sees each event.
:- multifile metta_memoized_dispatch_call/4.
:- multifile metta_on_function_changed/1.
:- multifile metta_on_function_removed/1.
:- multifile metta_on_definitions_settled/0.
:- multifile metta_on_runnable/1.

metta_memoized_dispatch_call(_, _, _, _) :- fail.
metta_on_function_changed(_).
metta_on_function_removed(_).
%The definitions in use are complete: before a runnable, and after a file.
metta_on_definitions_settled.
%A runnable is about to be compiled (its source term):
metta_on_runnable(_).
