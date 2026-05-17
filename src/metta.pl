%%%%%%%%%% Dependencies %%%%%%%%%%
library(X, Path) :- library_path(Base), atomic_list_concat([Base, '/', X], Path).
library(X, Y, Path) :- library_path(Base), atomic_list_concat([Base, '/../', X, '/', Y], Path).
:- prolog_load_context(directory, Source),
   directory_file_path(Source, '..', Parent),
   directory_file_path(Parent, 'lib', LibPath),
   asserta(library_path(LibPath)).
:- autoload(library(uuid)).
:- use_module(library(random)).
:- use_module(library(janus)).
:- use_module(library(error)).
:- use_module(library(listing)).
:- use_module(library(aggregate)).
:- use_module(library(thread)).
:- use_module(library(lists)).
:- use_module(library(yall), except([(/)/3])).
:- use_module(library(apply)).
:- use_module(library(apply_macros)).
:- use_module(library(process)).
:- use_module(library(filesex)).
:- ensure_loaded('he/he_boot').

:- current_prolog_flag(argv, Argv),
   set_metta_profile_from_args(Argv).

:- current_prolog_flag(argv, Argv),
   ( member(mork, Argv) -> ensure_loaded([parser, translator, specializer, filereader, '../mork_ffi/morkspaces', spaces])
                         ; ensure_loaded([parser, translator, specializer, filereader, spaces])).

%%%%%%%%%% Standard Library for MeTTa %%%%%%%%%%

%%% Representation and parsing conversions: %%%
id(X, X).
repr(Term, R) :- swrite(Term, R).
repra(Term, R) :- term_to_atom(Term, R).
parse(Str, R) :- sread(Str, R).

%%% Arithmetic & Comparison: %%%
'+'(A,B,R)  :- R is A + B.
'-'(A,B,R)  :- R is A - B.
'*'(A,B,R)  :- R is A * B.
'/'(A,B,R)  :- R is A / B.
'%'(A,B,R)  :- R is A mod B.
'<'(A,B,R)  :- (A<B -> R=true ; R=false).
'>'(A,B,R)  :- (A>B -> R=true ; R=false).
'=='(A,B,R) :- he_bridge_compare(eq, A, B, R), !.
'=='(A,B,R) :- (A==B -> R=true ; R=false).
'!='(A,B,R) :- he_bridge_compare(ne, A, B, R), !.
'!='(A,B,R) :- (A==B -> R=false ; R=true).
'='(A,B,R) :-  (A=B -> R=true ; R=false).
'=?'(A,B,R) :- (\+ \+ A=B -> R=true ; R=false).
'=alpha'(A,B,R) :- (A =@= B -> R=true ; R=false).
'=@='(A,B,R) :- (A =@= B -> R=true ; R=false).
'<='(A,B,R) :- (A =< B -> R=true ; R=false).
'>='(A,B,R) :- (A >= B -> R=true ; R=false).
min(A,B,R)  :- R is min(A,B).
max(A,B,R)  :- R is max(A,B).
exp(Arg,R) :- R is exp(Arg).
:- use_module(library(clpfd)).
'#+'(A, B, R) :- R #= A + B.
'#-'(A, B, R) :- R #= A - B.
'#*'(A, B, R) :- R #= A * B.
'#div'(A, B, R) :- R #= A div B.
'#//'(A, B, R) :- R #= A // B.
'#mod'(A, B, R) :- R #= A mod B.
'#min'(A, B, R) :- R #= min(A,B).
'#max'(A, B, R) :- R #= max(A,B).
'#<'(A, B, true)  :- A #< B, !.
'#<'(_, _, false).
'#>'(A, B, true)  :- A #> B, !.
'#>'(_, _, false).
'#='(A, B, true)  :- A #= B, !.
'#='(_, _, false).
'#\\='(A, B, true)  :- A #\= B, !.
'#\\='(_, _, false).
he_float_surface_number(Raw, Out) :-
    integer(Raw), !,
    Out is float(Raw).
he_float_surface_number(Raw, Raw).

he_list_prefers_float_surface([Value|_]) :-
    float(Value), !.
he_list_prefers_float_surface([_|Values]) :-
    he_list_prefers_float_surface(Values).

'pow-math'(A, B, ['Error', ['pow-math', A, B], ['MathDomainError', 2, 'IntegralExponentWhenBaseNegative']]) :-
    number(A),
    number(B),
    A < 0,
    B =\= round(B), !.
'pow-math'(A, B, ['Error', ['pow-math', A, B], ['MathDomainError', 1, 'NonZeroBaseWhenExponentNegative']]) :-
    number(A),
    number(B),
    A =:= 0,
    B < 0, !.
'pow-math'(A, B, Out) :-
    Raw is A ** B,
    he_float_surface_number(Raw, Out).
'sqrt-math'(A, ['Error', ['sqrt-math', A], ['MathDomainError', 1, 'NonNegativeReal']]) :-
    number(A),
    A < 0, !.
'sqrt-math'(A, Out)   :- Out is sqrt(A).
'abs-math'(A, Out)    :- Out is abs(A).
'log-math'(Base, X, ['Error', ['log-math', Base, X], ['MathDomainError', 1, 'PositiveRealNotOne']]) :-
    number(Base),
    ( Base =< 0 ; Base =:= 1 ), !.
'log-math'(Base, X, ['Error', ['log-math', Base, X], ['MathDomainError', 2, 'PositiveReal']]) :-
    number(X),
    X =< 0, !.
'log-math'(Base, X, Out) :- Out is log(X) / log(Base).
'trunc-math'(A, Out)  :- Raw is truncate(A), he_float_surface_number(Raw, Out).
'ceil-math'(A, Out)   :- Raw is ceil(A), he_float_surface_number(Raw, Out).
'floor-math'(A, Out)  :- Raw is floor(A), he_float_surface_number(Raw, Out).
'round-math'(A, Out)  :- Raw is round(A), he_float_surface_number(Raw, Out).
'sin-math'(A, Out)  :- Out is sin(A).
'cos-math'(A, Out)  :- Out is cos(A).
'tan-math'(A, Out)  :- Out is tan(A).
'asin-math'(A, ['Error', ['asin-math', A], ['MathDomainError', 1, 'ClosedUnitInterval']]) :-
    number(A),
    ( A < -1 ; A > 1 ), !.
'asin-math'(A, Out) :- Out is asin(A).
'acos-math'(A, ['Error', ['acos-math', A], ['MathDomainError', 1, 'ClosedUnitInterval']]) :-
    number(A),
    ( A < -1 ; A > 1 ), !.
'acos-math'(A, Out) :- Out is acos(A).
'atan-math'(A, Out) :- Out is atan(A).
'isnan-math'('NaN', true) :- !.
'isnan-math'(A, Out) :- number(A), !, ( A =:= A -> Out = false ; Out = true ).
'isinf-math'(inf, true) :- !.
'isinf-math'('-inf', true) :- !.
'isinf-math'(A, Out) :- number(A), !, ( A =:= 1.0Inf ; A =:= -1.0Inf -> Out = true ; Out = false ).
'min-atom'(List, Out) :-
    min_list(List, Raw),
    he_float_surface_number(Raw, Out).
'max-atom'(List, Out) :-
    max_list(List, Raw),
    he_float_surface_number(Raw, Out).

%%% Random Generators: %%%
'random-int'(Min, Max, Result) :- random_between(Min, Max, Result).
'random-int'('&rng', Min, Max, Result) :- random_between(Min, Max, Result).
'random-float'(Min, Max, Result) :- random(R), Result is Min + R * (Max - Min).
'random-float'('&rng', Min, Max, Result) :- random(R), Result is Min + R * (Max - Min).

%%% Boolean Logic: %%%
bool(true).
bool(false).
and(A,B,C) :- bool(A), bool(B), ( A == true -> C = B ; A == false -> C = false ).
or(A,B,C) :- bool(A), bool(B), ( A == true -> C = true ; A == false -> C = B ).
not(A,B) :- bool(A), ( A == true -> B = false ; A == false -> B = true ).
xor(A,B,C) :- bool(A), bool(B), ( A == B -> C = false ; C = true ).
implies(A,B,C) :- bool(A), bool(B), ( A == true -> ( B == true  -> C = true ; B == false -> C = false )
                                                 ; A == false -> C = true ).

%%% Nondeterminism: %%%
superpose(L,X) :- member(X,L).
empty(_) :- fail.

%%% Lists / Tuples: %%%
'cons-atom'(H, T, [H|T]).
'decons-atom'([H|T], [H|[T]]).
'first-from-pair'([A, _], A).
first([A, _], A).
'second-from-pair'([_, A], A).
'unique-atom'(A, B) :- list_to_set(A, B).

%%% Alpha-equivalence unique atom %%%
'alpha-unique-atom'(A, B) :-
    must_be(list, A),
    alpha_list_to_set(A, B).

alpha_list_to_set(List, Set) :-
    empty_assoc(Seen0),
    alpha_list_to_set_assoc(List, Seen0, Set).

alpha_list_to_set_assoc([], _, []).
alpha_list_to_set_assoc([H|T], SeenIn, R) :-
    copy_term(H, HCopy),
    numbervars(HCopy, 0, _),
    term_hash(HCopy, Key),
    ( get_assoc(Key, SeenIn, _) ->
        alpha_list_to_set_assoc(T, SeenIn, R)
    ;
        put_assoc(Key, SeenIn, true, SeenOut),
        R = [H|RT],
        alpha_list_to_set_assoc(T, SeenOut, RT)
    ).

'sort-atom'(List, Sorted) :- msort(List, Sorted).
'size-atom'(List, Size) :- length(List, Size).
'car-atom'(Arg, Out) :-
    he_profile_enabled,
    ( var(Arg)
    ; Arg == []
    ; \+ is_list(Arg)
    ), !,
    Out = ['Error', ['car-atom', Arg],
           "car-atom expects a non-empty expression as an argument"].
'car-atom'([H|_], H).
'cdr-atom'(Arg, Out) :-
    he_profile_enabled,
    ( var(Arg)
    ; Arg == []
    ; \+ is_list(Arg)
    ), !,
    Out = ['Error', ['cdr-atom', Arg],
           "cdr-atom expects a non-empty expression as an argument"].
'cdr-atom'([_|T], T).
decons([H|T], [H|[T]]).
cons(H, T, [H|T]).
'index-atom'(List, Index, Elem) :- nth0(Index, List, Elem).
member(X, L, true) :- member(X, L).
'is-member'(X, List, true) :- member(X, List).
'is-member'(X, List, false) :- \+ member(X, List).
'exclude-item'(A, L, R) :- exclude(==(A), L, R).

%Multisets:
'subtraction-atom'([], _, []).
'subtraction-atom'([H|T], B, Out) :- ( select(H, B, BRest) -> 'subtraction-atom'(T, BRest, Out)
                                                            ; Out = [H|Rest],
                                                              'subtraction-atom'(T, B, Rest) ).
'union-atom'(A, B, Out) :- append(A, B, Out).
'intersection-atom'(A, B, Out) :- intersection(A, B, Out).

%%% Diagnostics / Testing: %%%
'println!'(Arg, true) :- he_public_print_text(Arg, Text),
                         format('~w~n', [Text]).

'readln!'(Out) :- read_line_to_string(user_input, Str),
                  sread(Str, Out).

test(A,B,true) :-
                  he_public_term(A, APublic),
                  he_public_term(B, BPublic),
                  (APublic =@= BPublic -> E = '✅' ; E = '❌'),
                  swrite_public(A, RA),
                  swrite_public(B, RB),
                  format("is ~w, should ~w. ~w ~n", [RA, RB, E]),
                  (APublic =@= BPublic -> true ; halt(1)).

assert(Goal, true) :- ( call(Goal) -> true
                                    ; swrite(Goal, RG),
                                      format("Assertion failed: ~w~n", [RG]),
                                      halt(1) ).

%%% Time Retrieval: %%%
'current-time'(Time) :- get_time(Time).
'format-time'(Format, TimeString) :- get_time(Time), format_time(atom(TimeString), Format, Time).

%%% Python bindings: %%%
'py-call'(SpecList, Result) :- 'py-call'(SpecList, Result, []).
'py-call'([Spec|Args], Result, Opts) :- ( string(Spec) -> atom_string(A, Spec) ; A = Spec ),
                                        must_be(atom, A),
                                        ( sub_atom(A, 0, 1, _, '.')         % ".method"
                                          -> sub_atom(A, 1, _, 0, Fun),
                                             Args = [Obj|Rest],
                                             ( Rest == []
                                               -> compound_name_arguments(Meth, Fun, [])
                                                ; Meth =.. [Fun|Rest] ),
                                             py_call(Obj:Meth, Result, Opts)
                                           ; atomic_list_concat([M,F], '.', A) % "mod.fun"
                                             -> ( Args == []
                                                  -> compound_name_arguments(Call0, F, [])
                                                   ; Call0 =.. [F|Args] ),
                                                py_call(M:Call0, Result, Opts)
                                              ; ( Args == []                      % bare "fun"
                                                  -> compound_name_arguments(Call0, A, [])
                                                   ; Call0 =.. [A|Args] ),
                                                py_call(builtins:Call0, Result, Opts) ).

py_term_atom(Term, Atom) :-
    ( atom(Term) -> Atom = Term
    ; string(Term) -> atom_string(Atom, Term)
    ; term_to_atom(Term, Atom)
    ).

py_path_parts(Spec, Parts) :-
    py_term_atom(Spec, Atom),
    atomic_list_concat(Raw, '.', Atom),
    Raw \= [],
    Parts = Raw.

py_get_attr(Obj, Attr, Value) :-
    py_term_atom(Attr, AttrAtom),
    py_call(builtins:getattr(Obj, AttrAtom), Value).

py_resolve_attrs(Obj, [], Obj).
py_resolve_attrs(Obj, [Attr|Attrs], Value) :-
    py_get_attr(Obj, Attr, Next),
    py_resolve_attrs(Next, Attrs, Value).

py_resolve_path(Spec, Value) :-
    py_path_parts(Spec, [Module|Attrs]),
    catch(py_call(importlib:import_module(Module), Root), _, fail), !,
    py_resolve_attrs(Root, Attrs, Value).
py_resolve_path(Spec, Value) :-
    py_path_parts(Spec, [Builtin|Attrs]),
    py_call(importlib:import_module(builtins), Builtins),
    py_get_attr(Builtins, Builtin, Root),
    py_resolve_attrs(Root, Attrs, Value).

py_resolve_value(Atom, Value) :-
    atom(Atom),
    atom_concat('&', _, Atom),
    catch(nb_getval(Atom, Bound), _, fail), !,
    Value = Bound.
py_resolve_value(Value, Value).

py_callable(Value) :-
    catch(py_call(builtins:callable(Value), @(true)), _, fail).

py_call_callable(Callable0, Args, Result) :-
    py_resolve_value(Callable0, Callable),
    py_callable(Callable),
    compound_name_arguments(Call, '__call__', Args),
    py_call(Callable:Call, Result).

'py-atom'(Spec, Result) :-
    py_resolve_path(Spec, Result).

'py-dot'(Obj0, Attr, Result) :-
    py_resolve_value(Obj0, Obj),
    py_get_attr(Obj, Attr, Result).

%%% Eval: %%%
eval(C, Out) :- once(translate_expr(C, Goals, Out)),
                call_goals(Goals).

call_goals([]).
call_goals([G|Gs]) :- call(G), 
                      call_goals(Gs).

%%% Higher-Order Functions: %%%
'foldl-atom'([], Acc, _Func, Acc).
'foldl-atom'([H|T], Acc0, Func, Out) :- reduce([Func,Acc0,H], Acc1),
                                        'foldl-atom'(T, Acc1, Func, Out).

'map-atom'([], _Func, []).
'map-atom'([H|T], Func, [R|RT]) :- reduce([Func,H], R),
                                   'map-atom'(T, Func, RT).

'filter-atom'([], _Func, []).
'filter-atom'([H|T], Func, Out) :- ( reduce([Func,H], true) -> Out = [H|RT]
                                                             ; Out = RT ),
                                   'filter-atom'(T, Func, RT).

%%% Prolog interop: %%%
argv(K, Arg) :- current_prolog_flag(argv, Argv), nth0(K, Argv, A), ( atom_number(A, N) -> Arg = N ; Arg = A ).
import_prolog_function(N, true) :- register_fun(N).
'Predicate'([F|Args], Term) :- Term =.. [F|Args].
callPredicate(G, true) :- call(G).
assertzPredicate(G, true) :- assertz(G).
assertaPredicate(G, true) :- asserta(G).
retractPredicate(G, true) :- retract(G), !.
retractPredicate(_, false).

%%% Library / Import: %%%
ensure_metta_ext(Path, Path) :- file_name_extension(_, metta, Path), !.
ensure_metta_ext(Path, PathWithExt) :- file_name_extension(Path, metta, PathWithExt).

'import!'(Space, File, Out) :- he_bridge_import(Space, File, Out).

:- dynamic translator_rule/1.
'add-translator-rule!'(HV, true) :- ( translator_rule(HV)
                                      -> true ; assertz(translator_rule(HV)) ).

'remove-translator-rule!'(HV, true) :- retractall(translator_rule(HV)).

%%% Registration: %%%
:- dynamic fun/1.
register_fun(N) :-
    ( fun(N) -> true ; assertz(fun(N)) ),
    ( current_predicate(he_note_fun_registered/1)
    -> he_note_fun_registered(N)
    ;  true
    ).
:- maplist(register_fun, [superpose, empty, let, 'let*', '+','-','*','/', '%', min, max, 'change-state!', 'get-state', 'bind!',
                          '<','>','==', '!=', '=', '=?', '<=', '>=', and, or, xor, implies, not, sqrt, exp, log, cos, sin,
                          'first-from-pair', 'second-from-pair', 'car-atom', 'cdr-atom', 'unique-atom', 'alpha-unique-atom',
                          repr, repra, parse, 'println!', 'readln!', test, assert, nop, size, 'count-atoms',
                          'mm2-exec', atom_concat, atom_chars, copy_term, term_hash,
                          foldl, first, last, append, length, 'size-atom', sort, msort, member, 'is-member', 'exclude-item', list_to_set, maplist, eval, reduce, 'import!',
                          'new-space', 'add-atom', 'add-atom-nodup', 'remove-atom', 'get-atoms', match, 'with-space-snapshot', 'is-var', 'is-expr', 'is-space', 'get-mettatype',
                          decons, 'decons-atom', 'py-call', 'py-atom', 'py-dot', 'get-type', 'get-metatype', '=alpha', concat, sread, cons, reverse,
                          '#+','#-','#*','#div','#//','#mod','#min','#max','#<','#>','#=','#\\=','set_hook',
                          'union-atom', 'cons-atom', 'intersection-atom', 'subtraction-atom', 'index-atom', id,
                          'pow-math', 'sqrt-math', 'sort-atom','abs-math', 'log-math', 'trunc-math', 'ceil-math',
                          'floor-math', 'round-math', 'sin-math', 'cos-math', 'tan-math', 'asin-math','random-int','random-float',
                          'acos-math', 'atan-math', 'isnan-math', 'isinf-math', 'min-atom', 'max-atom',
                          'range-atom', 'repeat-atom', 'sort-strings', 'print-alternatives!',
                          'foldl-atom', 'map-atom', 'filter-atom','current-time','format-time', library, exists_file,
	                          'new-state', 'get-doc', 'help!',
	                          import_prolog_function, 'Predicate', callPredicate, assertaPredicate, assertzPredicate, retractPredicate,
	                          'add-translator-rule!', 'remove-translator-rule!', argv, 'pragma!',
	                          'register-module!', 'mod-space!', 'module-inventory!',
	                          'mork:new-space', 'mork:add-atom', 'mork:match', 'mork:size', 'mork:get-atoms',
	                          'mork:clone', 'mork:step!', 'mork:dump!', 'mork:open-act']).
:- ( metta_profile(Profile),
      current_predicate(install_profile/1)
   -> install_profile(Profile)
   ; true ).
'range-atom'(End, Out) :-
    integer(End),
    End > 0, !,
    End1 is End - 1,
    findall(I, between(0, End1, I), Out).
'range-atom'(End, []) :-
    integer(End),
    End =< 0, !.
'range-atom'(Start, End, []) :-
    integer(Start),
    integer(End),
    Start >= End, !.
'range-atom'(Start, End, Out) :-
    integer(Start),
    integer(End),
    Start < End,
    End1 is End - 1,
    findall(I, between(Start, End1, I), Out).
'repeat-atom'(Count, _Atom, Out) :-
    integer(Count),
    Count =< 0, !,
    Out = [].
'repeat-atom'(Count, Atom, Out) :-
    integer(Count),
    Count > 0,
    length(Out, Count),
    maplist(=(Atom), Out).
'sort-strings'(List, Sorted) :-
    is_list(List),
    maplist(string, List),
    msort(List, Sorted).
'print-alternatives!'(Label, Alts, []) :-
    is_list(Alts), !,
    length(Alts, Count),
    swrite(Label, LabelText),
    format('~w: ~w alternatives~n', [LabelText, Count]),
    forall(member(Alt, Alts),
           ( swrite(Alt, AltText),
             format('~w~n', [AltText]) )).
'print-alternatives!'(Label, Alts, ['Error', ['print-alternatives!', Label, Alts], 'Atom is not an ExpressionAtom']).
