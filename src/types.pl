%%%%%%%%%% Types: declared contracts, checked at compile time where possible %%%%%%%%%%
%
% (: f (-> A1 .. An R)) is a contract: f's arguments have the types A1 .. An and
% its results the type R. (-[det]-> ...) and (-[semidet]-> ...) are the same
% contract and additionally commit f to its first matching clause. TYPES.md gives
% the rules and the argument for them; this module is all of their implementation.
%
% The translator gives every value it produces a static type: a type term, or
% '%Undefined%' when nothing is known. A variable inside a static type is free:
% values such as () or (empty) fit every instance of it. At each boundary - an
% argument of a call, a function's result, (the T E) - type_boundary/4 chooses
% between nothing (the type is established), a compile-time error (two known
% types that no value has both of) and a runtime guard. A failing guard raises a
% type error: types never silently filter answers, so a program that runs
% without a type error runs the same with all of its types erased.

:- module(types, [ type_decl/5, native_builtin/1, note_type_decl/1, forget_type_decl/1,
                   unique_type_decl/5, clause_contract/6, type_arg_policy/3, type_normalize/2, add_builtin_signatures/2,
                   static_type/2, set_static_type/2, force_static_type/2, join_static_types/2,
                   strip_static_types/1, opaque_type/2, result_static_type/3, type_pattern/2,
                   type_boundary/4, type_boundary_args/4, type_overload/8, type_instantiate/2, cons_static_type/3,
                   typecheck_or_error/2, typecheck_ok/2, fn_type/4, dynamic_boundary/2, checked_params/3 ]).

:- dynamic type_decl/5, native_builtin/1, checked_params/3.
% type_decl(F, N, ArgTypes, OutType, Det) for each declaration of F with N arguments,
% Det is det, semidet or plain. Builtins implemented in Prolog are native_builtin/1:
% they test their own arguments, so calls to them need no guards.

%%% Declarations %%%

%Arrow spellings, giving the determinism the declared function commits to:
arrow('->', plain) :- !.
arrow('-[det]->', det) :- !.
arrow('-[semidet]->', semidet) :- !.
arrow(A, plain) :- atom(A), sub_atom(A, 0, _, _, '-['), sub_atom(A, _, _, 0, ']->').

%A function type, with nested arrows written -> and _ written %Undefined%:
fn_type(T, ArgTs, Out, Det) :- is_list(T), T = [A|Ts], atom(A), arrow(A, Det), append(As, [O], Ts), !,
                               maplist(type_normalize, As, ArgTs), type_normalize(O, Out).
type_normalize(T, T) :- var(T), !.
type_normalize('_', '%Undefined%') :- !.
type_normalize([A|Ts], ['->'|Ns]) :- atom(A), arrow(A, _), !, maplist(type_normalize, Ts, Ns).
type_normalize(T, N) :- is_list(T), !, maplist(type_normalize, T, N).
type_normalize(T, T).

%Called for every atom added to or removed from &self. A change to the
%declarations of a function already compiled recompiles it against them:
note_type_decl([C, F, T]) :- C == ':', atom(F), fn_type(T, As, O, D), !, length(As, N),
                             ( decl_exists(F, N, As, O) -> true
                             ; assertz(type_decl(F, N, As, O, D)), redeclared(F) ).
note_type_decl(_).
forget_type_decl([C, F, T]) :- C == ':', atom(F), fn_type(T, As, O, _), !, length(As, N),
                               forall(( clause(type_decl(F, N, As2, O2, _), true, Ref), [As2, O2] =@= [As, O] ), erase(Ref)),
                               redeclared(F).
forget_type_decl(_).
decl_exists(F, N, As, O) :- type_decl(F, N, As2, O2, _), [As2, O2] =@= [As, O], !.

redeclared(F) :- retractall(checked_params(F, _, _)),
                 forall(( unique_type_decl(F, N, As, _, _),
                          maplist([A, C]>>( closed(A), \+ wildcard(A) -> C = A ; C = '%Undefined%' ), As, Cs),
                          \+ maplist(==('%Undefined%'), Cs) ),
                        assertz(checked_params(F, N, Cs))),
                 ( translated_from(_, [=, [G|_], _]), G == F
                   -> format(user_error, "Warning: the type declarations of ~w changed after its definition; recompiling it~n", [F]),
                      recompile_function_clauses(F)
                    ; true ).

%Declarations of the builtins (lib_builtin_types adds them to &self for get-type):
builtin_type(F, ['->'|Ts]) :- member(Fs-Ts, [ ['+','-','*','/','%',min,max,'pow-math','log-math']-['Number','Number','Number'],
                                               [exp,'sqrt-math','abs-math','trunc-math','ceil-math','floor-math','round-math',
                                                'sin-math','asin-math','cos-math','acos-math','tan-math','atan-math']-['Number','Number'],
                                               ['<','>','<=','>=']-['Number','Number','Bool'],
                                               ['isnan-math','isinf-math']-['Number','Bool'],
                                               [and,or,xor,implies]-['Bool','Bool','Bool'],
                                               [not]-['Bool','Bool'],
                                               ['==','!=','=','=?','=alpha','=@=','@<','@>','@<=','@>=']-[_,_,'Bool'],
                                               ['min-atom','max-atom','size-atom']-[_,'Number'],
                                               ['is-var','is-ground','is-expr','is-space']-[_,'Bool'],
                                               ['random-int','random-float']-['Number','Number','Number'],
                                               [repr]-[_,'String'],
                                               [empty]-[_] ]),
                              member(F, Fs).
:- forall(builtin_type(F, T), ( fn_type(T, As, O, D), length(As, N),
                                assertz(type_decl(F, N, As, O, D)), assertz(native_builtin(F)) )).
add_builtin_signatures(Space, true) :- forall(builtin_type(F, T), 'add-atom'(Space, [':', F, T], true)).

%The declaration a clause of F/N is compiled against: the only one there is.
unique_type_decl(F, N, As, O, D) :- findall(d(As0, O0, D0), type_decl(F, N, As0, O0, D0), [d(As, O, D)]).

%The contract a clause of F/N is compiled against: of F's declarations, those
%its constant head arguments can fit, instantiated by them. One gives the
%parameter types PTs (opaque, see opaque_type/2), the result type and the
%commitment; several leave the clause unchecked, since each call is checked
%against the declarations its arguments fit; none is an error.
clause_contract(F, N, Args, PTs, OT, Det) :-
    findall(d(As, O, D), type_decl(F, N, As, O, D), Ds),
    include({Args}/[d(As, _, _)]>>( instantiate(Args, As),
                                    \+ ( nth1(I, Args, V), nth1(I, As, T), static_type(V, S), conflict(S, T) ) ), Ds, Fits),
    ( Fits = [d(As, O, D)] -> opaque_type(As-O, PTs-OT), Det = D
    ; Ds \== [], Fits == [] -> throw(error(no_matching_overload(F), typecheck))
    ; OT = '%Undefined%', Det = plain ).

%Argument positions that every declaration of F/N types Atom stay unevaluated.
%The result is a list of types for translate_args_by_type/4: Atom or unknown.
type_arg_policy(F, N, Ps) :- findall(As, type_decl(F, N, As, _, _), Ass), Ass \== [],
                             length(Ps, N),
                             foldl({Ass}/[P, I, J]>>( J is I + 1,
                                                     ( forall(member(As, Ass), (nth1(I, As, A), A == 'Atom')) -> P = 'Atom' ; true ) ),
                                   Ps, 1, _).

%%% Static types of translated values %%%

wildcard(T) :- atom(T), memberchk(T, ['%Undefined%', 'Atom', 'Expression']).

static_type(V, T) :- var(V), !, ( get_attr(V, pt, T0) -> T = T0 ; T = '%Undefined%' ).
static_type(V, 'Number') :- number(V), !.
static_type(V, 'String') :- string(V), !.
static_type(V, 'Bool') :- ( V == true ; V == false ), !.
static_type([], ['List', _]) :- !.
static_type(V, T) :- atom(V), fun(V), callable_type(V, 0, T), !.
static_type(partial(F, Bs), T) :- atom(F), is_list(Bs), length(Bs, K), callable_type(F, K, T), !.
static_type([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N), unique_type_decl(C, N, As, O, _),
                          instantiate(Fs, As), maplist(value_established, Fs, As), !, result_static_type(As, O, T).
static_type([X|Xs], ['List', T]) :- is_list(Xs), !, maplist(static_type, [X|Xs], Ts), join_static_types(Ts, T).
static_type(_, '%Undefined%').

%A function, or its partial application to K arguments, as a value:
callable_type(F, K, ['->'|Ts]) :- findall(As-O, (type_decl(F, N, As, O, _), N > K), [As-O]),
                                  length(Bound, K), append(Bound, Rest, As), append(Rest, [O], Ts).

set_static_type(V, T) :- var(V), \+ T == '%Undefined%', !, put_attr(V, pt, T).
set_static_type(_, _).
force_static_type(V, T) :- ( var(V) -> ( T == '%Undefined%' -> del_attr(V, pt) ; put_attr(V, pt, T) ) ; true ).
%Two typed variables unified at compile time keep a type only if they agree:
pt:attr_unify_hook(T, Y) :- ( var(Y), get_attr(Y, pt, T2), T2 \=@= T -> del_attr(Y, pt) ; true ).
strip_static_types(Term) :- term_attvars(Term, Vs), maplist([V]>>del_attr(V, pt), Vs).

%cons and cons-atom build a list whose elements have what the head and the
%tail's elements agree on:
cons_static_type(H, Tl, ['List', E]) :- static_type(Tl, TT), list_type(TT, E0), !,
                                        static_type(H, S), join_static_types([S, E0], E).
cons_static_type(_, _, '%Undefined%').

%The type of a merge of alternatives (if, case, superpose): what all agree on.
join_static_types(Ts, T) :- copy_term(Ts, [T0|Rest]), ( maplist(=(T0), Rest) -> T = T0 ; T = '%Undefined%' ).

%%% Relations between a static type S and a required type T %%%

%Established: every value of type S satisfies T. Free variables of S are
%copied (a bottom value fits each use), variables of T stand for any type.
value_established(V, T) :- static_type(V, S), established(S, T).
established(S, T) :- \+ \+ ( copy_term(S, S1), est(S1, T) ).
est(S, T) :- var(T), !, T = S.
est(S, T) :- var(S), !, S = T.
est(_, T) :- wildcard(T), !.
est(S, _) :- wildcard(S), !, fail.
est(S, T) :- list_type(S, SE), !, list_type(T, TE), est(SE, TE).
est(_, T) :- list_type(T, _), !, fail.                          %a list is never a tuple
est(S, [U|Ts]) :- U == '|', !, member(T, Ts), est(S, T), !.
est([U|Ss], T) :- U == '|', !, forall(member(S, Ss), est(S, T)).
est(S, T) :- ( atom(T) ; rigid(T) ), !, S == T.
est(S, T) :- is_list(S), is_list(T), same_length(S, T), maplist(est, S, T).

%A conflict: no value has both types. Only the shapes of primitive, list and
%arrow types are disjoint, since get-type may give any other value any other type.
conflict(S, T) :- ( var(S) ; var(T) ), !, fail.
conflict(S, T) :- rigid(S), !, \+ wildcard(T), S \== T.     %a parametric value used at another type
conflict([U|Ss], T) :- U == '|', !, forall(member(S, Ss), conflict(S, T)).
conflict(S, [U|Ts]) :- U == '|', !, forall(member(T, Ts), conflict(S, T)).
conflict(S, T) :- list_type(S, SE), list_type(T, TE), !, conflict(SE, TE).
conflict(S, T) :- shape(S, A), shape(T, B), A \== B.
shape(T, T) :- atom(T), memberchk(T, ['Number', 'String', 'Bool']), !.
shape(T, list) :- list_type(T, _), !.
shape(T, arrow) :- nonvar(T), T = [A|_], A == '->'.

%(List E), tested without binding a variable in the head of a tuple type:
list_type(T, E) :- nonvar(T), T = [L, E], L == 'List'.

%Instantiate a fresh declaration instance with what the arguments establish,
%before any argument is checked, so the result is independent of their order:
type_instantiate(Vs, Ts) :- instantiate(Vs, Ts).
instantiate(Vs, Ts) :- maplist([V, T]>>( static_type(V, S), ( learn(S, T) -> true ; true ) ), Vs, Ts).
learn(S, _) :- ( var(S) ; wildcard(S) ), !.
learn(S, T) :- var(T), !, ( \+ ( sub_term(X, S), atom(X), wildcard(X) ) -> copy_term(S, T) ; true ).
learn(_, T) :- wildcard(T), !.
learn(S, T) :- list_type(S, SE), !, ( list_type(T, TE) -> learn(SE, TE) ; true ).
learn(_, T) :- list_type(T, _), !.
learn(S, T) :- is_list(S), is_list(T), S = [H|_], \+ H == '|', same_length(S, T), !, maplist(learn, S, T).
learn(_, _).

%The result type of a call: the declared result under that instance. Type
%variables the arguments left open are unknown, unless no argument mentions
%them: such a result, like (empty)'s, fits every type.
result_static_type(ArgTs, Out, T) :- term_variables(ArgTs, Open), close_type(Open, Out, T).
close_type(Open, T0, T) :- var(T0), !, ( member(V, Open), V == T0 -> T = '%Undefined%' ; T = T0 ).
close_type(Open, T0, T) :- is_list(T0), !, maplist(close_type(Open), T0, T).
close_type(_, T, T).

%A function's own declaration as seen from its body: each type variable is
%the caller's choice, a rigid type that equals only itself.
opaque_type(T, O) :- copy_term(T, O), term_variables(O, Vs), foldl([V, I, J]>>( V = '$rigid'(I), J is I + 1 ), Vs, 1, _).
rigid(T) :- compound(T), T = '$rigid'(_).
forget_rigid(T, U) :- rigid(T), !, U = '%Undefined%'.
forget_rigid(T, U) :- is_list(T), !, maplist(forget_rigid, T, U).
forget_rigid(T, T).
%Closed types can be checked at runtime; a variable or rigid one is trusted:
closed(T) :- ground(T), \+ ( sub_term(X, T), rigid(X) ).

%%% Boundaries %%%

%type_boundary(Ctx, V, T, Goals): what passing value V where T is required
%needs. (the T E) casts through the dynamic type, forgetting rigid types.
type_boundary(_, _, T, []) :- ( var(T) ; wildcard(T) ), !.
type_boundary(Ctx, V, T, Gs) :- static_type(V, S0), ( Ctx = the(_) -> forget_rigid(S0, S) ; S = S0 ),
                                boundary(Ctx, V, S, T, Gs).
boundary(_, _, S, T, []) :- established(S, T), !.
boundary(_, V, S, T, _) :- conflict(S, T), !,
                           ( ground(V), \+ rigid(S) -> throw(error(literal_type_mismatch(V, T), typecheck))
                                                     ; throw(error(type_conflict(existing(S), required(T)), typecheck)) ).
boundary(_, _, _, T, []) :- \+ closed(T), !.          %polymorphic content is trusted
boundary(native, _, _, _, []) :- !.                    %a native builtin tests its own arguments
boundary(Ctx, V, _, T, [G]) :- guard(V, T, G),
                                 ( warn_runtime_checks(true)
                                   -> ( nb_current('$compiling', F), F \== none -> true ; F = 'a runnable' ),
                                      format(user_error, "Warning: runtime type check of ~w against ~p in ~w~n", [Ctx, T, F])
                                    ; true ).

%The arguments of a call against a fresh declaration instance:
type_boundary_args(Ctx, Vs, Ts, Goals) :- instantiate(Vs, Ts), maplist(type_boundary(Ctx), Vs, Ts, Gss), append(Gss, Goals).

%Several declarations of Fun: those the arguments may fit are tried in order
%at runtime, and the result must fit one that accepted the arguments.
type_overload(Ctx, Fun, AVs, Out, Ds, Checks, Extra, Type) :-
        include({Ctx, AVs}/[d(As, _)]>>catch(\+ \+ type_boundary_args(Ctx, AVs, As, _), error(_, typecheck), fail), Ds, Fits),
        ( Fits == [] -> throw(error(no_matching_overload(Fun), typecheck)) ; true ),
        maplist(overload_tests(AVs, Out), Fits, ArgTests, JointTests, Types),
        join_static_types(Types, Type),
        disjunction(ArgTests, AnyArgs), disjunction(JointTests, AnyJoint),
        Fits = [d(_, O1)|_],
        Checks = [( AnyArgs -> true ; throw(error(no_matching_overload(Fun), typecheck)) )],
        Extra = [( AnyJoint -> true ; throw(error(literal_type_mismatch(Out, O1), typecheck)) )].
overload_tests(AVs, Out, d(As0, O0), ArgTest, (ArgTest, OutTest), Type) :-
        copy_term(As0-O0, As-O), instantiate(AVs, As),
        foldl([V, T, G0, G]>>( value_established(V, T) -> G = G0 ; ground(T) -> G = (G0, typecheck_ok(V, T)) ; G = G0 ),
              AVs, As, true, ArgTest),
        ( ground(O) -> OutTest = typecheck_ok(Out, O) ; OutTest = true ),
        result_static_type(As, O, Type).
disjunction([G], G) :- !.
disjunction([G|Gs], (G ; R)) :- disjunction(Gs, R).

%%% Runtime %%%

%A call whose callee is known only at runtime (a closure, reduce) checks the
%callee's closed parameter types here, as a known call site would statically:
dynamic_boundary(F, Args) :- ( length(Args, N), checked_params(F, N, Ts) -> maplist(typecheck_or_error, Args, Ts) ; true ).

guard(V, 'Number', (number(V) -> true ; typecheck_or_error(V, 'Number'))) :- !.
guard(V, 'String', (string(V) -> true ; typecheck_or_error(V, 'String'))) :- !.
guard(V, 'Bool', ((V == true ; V == false) -> true ; typecheck_or_error(V, 'Bool'))) :- !.
guard(V, T, typecheck_or_error(V, T)).

typecheck_or_error(V, T) :- ( typecheck_ok(V, T) -> true ; throw(error(literal_type_mismatch(V, T), typecheck)) ).

%The value relation. An unbound value fits every type: a check describes the
%value as it is, it does not constrain later bindings.
typecheck_ok(V, _) :- var(V), !.
typecheck_ok(_, T) :- var(T), !.
typecheck_ok(V, 'Number') :- !, number(V).
typecheck_ok(V, 'String') :- !, string(V).
typecheck_ok(V, 'Bool') :- !, ( V == true -> true ; V == false ).
typecheck_ok(_, T) :- wildcard(T), !.
typecheck_ok(V, T) :- list_type(T, E), !, list_ok(V, E).
typecheck_ok(V, [A|Ts]) :- A == '->', !, length(Ts, N), callable_arity(V, N).
typecheck_ok(V, [U|Ts]) :- U == '|', !, member(T, Ts), typecheck_ok(V, T), !.
%A constructor application fits by its declaration, a tuple field by field
%(a type's atom head may be the value's literal tag); anything else as get-type says:
typecheck_ok([C|Fs], T) :- atom(C), is_list(Fs), length(Fs, N), type_decl(C, N, As, O, _),
                           \+ \+ ( O = T, maplist(typecheck_ok, Fs, As) ), !.
typecheck_ok(V, Ts) :- is_list(Ts), is_list(V), same_length(V, Ts),
                       maplist([X, T]>>( X == T, atom(T) -> true ; typecheck_ok(X, T) ), V, Ts), !.
typecheck_ok(V, T) :- \+ \+ ( 'get-type'(V, T) ; 'get-metatype'(V, T) ).
%A function, or a partial application, taking N - 1 more arguments:
callable_arity(F, N) :- atom(F), !, arity(F, N).
callable_arity(partial(F, Bs), N) :- atom(F), length(Bs, K), M is N + K, arity(F, M).
list_ok(V, _) :- var(V), !.
list_ok([], _) :- !.
list_ok([X|Xs], T) :- typecheck_ok(X, T), list_ok(Xs, T).

%%% Patterns %%%

%The variables of a pattern matched against a value of type T get the types
%that T gives them; nothing is learned where T says nothing.
type_pattern(P, T) :- copy_term(T, T1), bind_pattern(P, T1).
bind_pattern(P, T) :- var(P), !, ( get_attr(P, pt, _) -> true ; set_static_type(P, T) ).
bind_pattern(_, T) :- ( var(T) ; wildcard(T) ), !.
bind_pattern(P, T) :- list_type(T, E), !, ( P = [H|R] -> bind_pattern(H, E), bind_pattern(R, T) ; true ).
bind_pattern([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N), unique_type_decl(C, N, As, O, _), O = T, !,
                           maplist(bind_pattern, Fs, As).
bind_pattern(Ps, [H|Ts]) :- is_list(Ps), ( var(H) ; is_list(H) ; shape(H, _) ; wildcard(H) ; rigid(H) ),
                            same_length(Ps, [H|Ts]), !, maplist(bind_pattern, Ps, [H|Ts]).
bind_pattern(_, _).

%--warn-runtime-checks reports each runtime guard the compiler emits:
warn_runtime_checks(true) :- current_prolog_flag(argv, Argv), memberchk('--warn-runtime-checks', Argv).
