%%%%%%%%%% Types: declared contracts, checked at compile time where possible %%%%%%%%%%
%
% (: f (-> A1 .. An R)) is a contract: f's arguments have the types A1 .. An and
% its results the type R. (-[det]-> ...) and (-[semidet]-> ...) are the same
% contract and also commit f to its first matching clause. TYPES.md gives the
% rules and the argument for them; this module is all of their implementation.
%
% The translator gives each value it produces a static type: a type term, or
% %Undefined% when nothing is known. At each boundary - an argument of a call,
% a function's result, (the T E) - type_boundary/4 compares the value's static
% type S with the required type T:
%   S establishes T               -> nothing to do,
%   S and T are not consistent    -> a type error at compile time,
%   otherwise                     -> a check at runtime of what is known of T.
% A failing check raises a type error: types never filter answers, so a run
% without type errors computes what the program computes with its types erased.

:- module(types, [ note_type_decl/1, forget_type_decl/1, note_function/1, note_foreign/1,     % declarations
                   type_decl/5, checked_params/3, add_builtin_signatures/2, fn_type/4, type_normalize/2,
                   clause_contract/6, type_arg_policy/3,                                    % compiling a clause
                   static_type/2, set_static_type/2, merge_static_type/2, strip_static_types/1,
                   type_boundary/4, type_call/6, type_closure_call/4,                        % boundaries
                   type_pattern/2, type_element_var/2,
                   typecheck_ok/2, typecheck_or_error/2, dynamic_boundary/2 ]).             % runtime

%%% Declarations %%%

:- dynamic type_decl/5, symbol_type/2, native_builtin/1, foreign/1, checked_params/3, get_type_extended/0.
% type_decl(F, N, ArgTypes, OutType, Det) for each declaration of F with N
% arguments, Det being det, semidet or plain; symbol_type(S, T) for each (: S T)
% giving a symbol a type that is not an arrow. native_builtin(F): a builtin
% implemented in Prolog, which tests its own arguments. foreign(F): a function
% imported from Prolog, whose results are not trusted.

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

%Called for every atom added to or removed from &self:
note_type_decl([C, _, T]) :- C == ':', is_list(T), T = [H|Ts], \+ ( atom(H), arrow(H, _) ),
                             member(A, Ts), atom(A), arrow(A, _), !,
                             throw(error(syntax_error('Arrows are prefix: write (-> A B), not (A -> B)'), _)).
note_type_decl([C, F, T]) :- C == ':', atom(F), fn_type(T, As, O, D), !, length(As, N),
                             ( type_decl(F, N, As2, O2, _), [As2, O2] =@= [As, O] -> true
                             ; assertz(type_decl(F, N, As, O, D)), redeclared(F) ).
note_type_decl([C, S, T0]) :- C == ':', atom(S), !, type_normalize(T0, T),
                              ( symbol_type(S, T1), T1 =@= T -> true ; assertz(symbol_type(S, T)) ).
note_type_decl(_).
forget_type_decl([C, F, T]) :- C == ':', atom(F), fn_type(T, As, O, _), !, length(As, N),
                               forall(( clause(type_decl(F, N, As2, O2, _), true, Ref), [As2, O2] =@= [As, O] ), erase(Ref)),
                               redeclared(F).
forget_type_decl([C, S, T0]) :- C == ':', atom(S), !, type_normalize(T0, T),
                                forall(( clause(symbol_type(S, T1), true, Ref), T1 =@= T ), erase(Ref)).
forget_type_decl(_).

%A change to F's declarations renews the parameter types that calls through a
%closure check (see dynamic_boundary/2) and recompiles F's clauses against them:
redeclared(F) :- retractall(checked_params(F, _, _)),
                 forall(( \+ type_flag('--no-type-checks'), unique_type_decl(F, N, As, _, _),
                          maplist(checkable, As, Cs), \+ maplist(wildcard, Cs) ),
                        assertz(checked_params(F, N, Cs))),
                 ( translated_from(_, [=, [G|_], _]), G == F
                   -> format(user_error, "Warning: the type declarations of ~w changed after its definition; recompiling it~n", [F]),
                      recompile_function_clauses(F)
                    ; true ).

%Called for every function defined: get-type rules of the program may give any
%value any type, so they open every type name (see consistent/2).
note_function(F) :- ( F == 'get-type', \+ get_type_extended -> assertz(get_type_extended) ; true ).
note_foreign(F) :- ( foreign(F) -> true ; assertz(foreign(F)) ).

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

unique_type_decl(F, N, As, O, D) :- findall(d(As0, O0, D0), type_decl(F, N, As0, O0, D0), [d(As, O, D)]).

%The contract a clause of F/N is compiled against: of F's declarations, those
%its constant head arguments can fit, instantiated by them. One gives the
%parameter and result types as seen from the body (see body_contract/4) and the
%commitment; several leave the clause unchecked, since each call is checked
%against the declarations its arguments fit; none is an error.
clause_contract(F, N, Args, PTs, OT, Det) :-
    findall(d(As, O, D), type_decl(F, N, As, O, D), Ds),
    include({Args}/[d(As, _, _)]>>( instantiate(Args, As),
                                    \+ ( nth1(I, Args, V), nth1(I, As, T), static_type(V, S), conflict(S, T) ) ), Ds, Fits),
    ( Fits = [d(As, O, D)] -> body_contract(As, O, PTs, OT), Det = D
    ; Ds \== [], Fits == [], \+ type_flag('--no-type-checks') -> throw(error(no_matching_overload(F), typecheck))
    ; OT = '%Undefined%', Det = plain ).

%Argument positions that every declaration of F/N types Atom stay unevaluated.
%The result is a list of types for translate_args_by_type/4: Atom or unknown.
type_arg_policy(F, N, Ps) :- findall(As, type_decl(F, N, As, _, _), Ass), Ass \== [],
                             length(Ps, N),
                             foldl({Ass}/[P, I, J]>>( J is I + 1,
                                                     ( forall(member(As, Ass), (nth1(I, As, A), A == 'Atom')) -> P = 'Atom' ; true ) ),
                                   Ps, 1, _).

%%% Static types %%%

%Types every value has: %Undefined% (nothing known), Atom and Expression:
wildcard(T) :- atom(T), memberchk(T, ['%Undefined%', 'Atom', 'Expression']).
primitive(T) :- atom(T), memberchk(T, ['Number', 'String', 'Bool']).

%A variable inside a static type is free: the value fits every instance of it,
%as () fits (List $a) for every $a.
static_type(V, T) :- var(V), !, ( get_attr(V, pt, T0) -> T = T0 ; T = '%Undefined%' ).
%A head argument of the clause being compiled, rebuilt in its body, is the argument:
static_type(V, T) :- compound(V), nb_current('$params', Ps-Ts), nonvar(Ts), nth1(I, Ps, P), P == V, !, nth1(I, Ts, T).
static_type(V, 'Number') :- number(V), !.
static_type(V, 'String') :- string(V), !.
static_type(V, 'Bool') :- ( V == true ; V == false ), !.
static_type([], ['List', _]) :- !.
static_type(V, T) :- atom(V), ( fun(V) ; type_decl(V, _, _, _, _) ), callable_type(V, 0, T), !.
static_type(V, T) :- atom(V), !, ( findall(T0, symbol_type(V, T0), [T]) -> true ; T = '%Undefined%' ).
static_type(partial(F, Bs), T) :- atom(F), is_list(Bs), length(Bs, K), callable_type(F, K, T), !.
%A constructor application has its declared type, if its fields establish it:
static_type([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N), type_decl(C, N, _, _, _), !,
                          ( unique_type_decl(C, N, As, O, _), instantiate(Fs, As), maplist(value_established, Fs, As)
                            -> result_static_type(constructor, As, O, T) ; T = '%Undefined%' ).
%Other data is a list of the type its elements agree on, else the tuple of their
%types, headed by the head symbol itself if it has no type (a tag, see typecheck_ok/2):
static_type([X|Xs], T) :- is_list(Xs), !, maplist(static_type, [X|Xs], [S|Ss]),
                          ( agreed_type([S|Ss], E) -> T = ['List', E] ; atom(X), S == '%Undefined%' -> T = [X|Ss] ; T = [S|Ss] ).
static_type(_, '%Undefined%').

%A function, or its partial application to K arguments, as a value: the rest of
%its declared arrow, or of the arrow of its arity if it has no declaration:
callable_type(F, K, ['->'|Ts]) :- findall(As-O, (type_decl(F, N, As, O, _), N > K), [As-O]), !,
                                  length(Bound, K), append(Bound, Rest, As), append(Rest, [O], Ts).
callable_type(F, K, ['->'|Ts]) :- \+ type_decl(F, _, _, _, _), findall(A, arity(F, A), [A]), N is A - K, N > 1,
                                  length(Ts, N), maplist(=('%Undefined%'), Ts).

set_static_type(V, T) :- var(V), \+ T == '%Undefined%', !, put_attr(V, pt, T).
set_static_type(_, _).
%A merge of alternatives (if, case, superpose, a fold's start and steps) has the
%type they agree on, else the union of theirs:
merge_static_type(V, Ts) :- merged_type(Ts, T), ( var(V) -> ( T == '%Undefined%' -> del_attr(V, pt) ; put_attr(V, pt, T) ) ; true ).
merged_type(Ts, T) :- agreed_type(Ts, T), !.
merged_type(Ts, T) :- foldl(add_alternative, Ts, [], Rs), reverse(Rs, Alts), ( Alts = [T] -> true ; T = ['|'|Alts] ).
agreed_type(Ts, T) :- copy_term(Ts, [T|Rest]), maplist(=(T), Rest).
add_alternative(T, Alts, Alts1) :- ( nonvar(T), T = [U|Ts], U == '|' -> foldl(add_alternative, Ts, Alts, Alts1)
                                   ; member(A, Alts), A =@= T -> Alts1 = Alts
                                   ; Alts1 = [T|Alts] ).
%Two typed variables unified at compile time keep a type only if they agree:
pt:attr_unify_hook(T, Y) :- ( var(Y), get_attr(Y, pt, T2), T2 \=@= T -> del_attr(Y, pt) ; true ).
strip_static_types(Term) :- term_attvars(Term, Vs), maplist([V]>>del_attr(V, pt), Vs).

%%% Relations between a static type S and a required type T %%%

%Established: every value of type S satisfies T. Free variables of S are
%copied (a bottom value fits each use), variables of T stand for any type.
value_established(V, T) :- static_type(V, S), established(S, T), !.
value_established(V, T) :- ground(V), closed(T), typecheck_ok(V, T).    %checked once, at compile time
established(S, T) :- \+ \+ ( copy_term(S, S1), est(S1, T) ).
est(S, T) :- var(T), !, T = S.
est(S, T) :- var(S), !, S = T.
est(_, T) :- wildcard(T), !.
est(S, _) :- wildcard(S), !, fail.
est([U|Ss], T) :- U == '|', !, forall(member(S, Ss), est(S, T)).
est(S, [U|Ts]) :- U == '|', !, member(T, Ts), est(S, T), !.
est(S, T) :- list_type(S, SE), !, list_type(T, TE), est(SE, TE).
est(S, T) :- list_type(T, TE), !, tuple_type(S), maplist({TE}/[X]>>est(X, TE), S).
est(S, T) :- ( atom(T) ; rigid(T) ), !, S == T.
est(S, T) :- is_list(S), is_list(T), same_length(S, T), maplist(est, S, T).

%Consistency (Siek and Taha): two types are consistent unless they disagree
%where both are known. A variable, a wildcard or a metatype is consistent with
%every type. Every alternative of a union S must be consistent with T, and some
%alternative of a union T with S. A value of a rigid type is used only at that
%type, while any value may be returned at it (trusted, see TYPES.md). Types
%that are not consistent are a conflict, a type error at compile time.
conflict(S, T) :- \+ consistent(S, T).
consistent(S, T) :- ( var(S) ; var(T) ; unknown(S) ; unknown(T) ), !.
consistent([U|Ss], T) :- U == '|', !, forall(member(S, Ss), consistent(S, T)).
consistent(S, [U|Ts]) :- U == '|', !, once(( member(T, Ts), consistent(S, T) )).
consistent(S, T) :- rigid(S), !, S == T.
consistent(_, T) :- rigid(T), !.
consistent(S, T) :- atom(S), atom(T), !, ( S == T -> true ; may_share_values(S, T) ).
consistent(S, T) :- atom(S), !, constructed(S, T).
consistent(S, T) :- atom(T), !, constructed(T, S).
consistent(S, T) :- list_type(S, E), tuple_type(T), !, maplist(consistent(E), T).     %a tuple is a list
consistent(S, T) :- tuple_type(S), list_type(T, E), !, maplist({E}/[X]>>consistent(X, E), S).
consistent(S, T) :- is_list(S), is_list(T), same_length(S, T), maplist(consistent, S, T).
unknown(T) :- wildcard(T), ! ; atom(T), ( memberchk(T, ['Symbol', 'Grounded', 'Variable']) -> true ; open_type_name(T) ).

%Type names are closed: the values of Number, String and Bool are fixed, those
%of a declared name are the symbols and constructor applications declared with
%it, so two names share values only through a symbol or constructor declared
%with both - unless get-type rules of the program open every non-primitive name.
may_share_values(S, T) :- symbol_type(X, S), symbol_type(X, T), !.
may_share_values(S, T) :- type_decl(C, N, _, S, _), \+ fun(C), type_decl(C, N, _, T, _), !.
open_type_name(T) :- get_type_extended, \+ primitive(T).
%A tuple type may be that of an application of one of a name's constructors:
constructed(Name, [C|Fs]) :- tuple_type([C|Fs]), ( var(C) ; unknown(C) ; length(Fs, N), type_decl(C, N, _, O, _), O == Name ), !.

%(List E), tested without binding a variable in the head of a tuple type, and
%a tuple type: the type of a fixed-length expression (a constructor's, too):
list_type(T, E) :- nonvar(T), T = [L, E], L == 'List'.
tuple_type(T) :- is_list(T), T = [H|_], H \== '->', H \== '|', \+ list_type(T, _).

%%% Declaration instances %%%

%Instantiate a fresh declaration instance with what the arguments establish,
%before any argument is checked, so the result is independent of their order:
instantiate(Vs, Ts) :- maplist([V, T]>>( static_type(V, S), ( learn(S, T) -> true ; true ) ), Vs, Ts).
learn(S, _) :- ( var(S) ; wildcard(S) ), !.
learn(S, T) :- var(T), !, ( \+ ( sub_term(X, S), atom(X), wildcard(X) ) -> copy_term(S, T) ; true ).
learn(_, T) :- wildcard(T), !.
learn(S, T) :- list_type(S, SE), !, ( list_type(T, TE) -> learn(SE, TE) ; true ).
learn(_, T) :- list_type(T, _), !.
learn(S, T) :- is_list(S), is_list(T), S = [H|_], \+ H == '|', same_length(S, T), !, maplist(learn, S, T).
learn(_, _).

%The result type of a call: the declared result under that instance. Type
%variables left open are unknown - those that no argument mentions are the
%function's own choice - except in the exact result of a builtin or of a
%constructor, where they fit every type, like (empty)'s.
result_static_type(Ctx, ArgTs, Out, T) :- term_variables(ArgTs, Open), close_type(Ctx, Open, Out, T).
close_type(Ctx, Open, T0, T) :- var(T0), !, ( memberchk(Ctx, [native, constructor]), \+ ( member(V, Open), V == T0 )
                                               -> T = T0 ; T = '%Undefined%' ).
close_type(Ctx, Open, T0, T) :- is_list(T0), !, maplist(close_type(Ctx, Open), T0, T).
close_type(_, _, T, T).

%A function's own declaration as seen from its body: a type variable of its
%parameters is the caller's choice, a rigid type that equals only itself; one
%that only the result mentions is the function's own choice, so it is unknown.
body_contract(As, O, PTs, OT) :- copy_term(As-O, PTs-OT), term_variables(PTs, Vs),
                                 foldl([V, I, J]>>( V = '$rigid'(I), J is I + 1 ), Vs, 1, _),
                                 term_variables(OT, Ws), maplist(=('%Undefined%'), Ws).
rigid(T) :- compound(T), T = '$rigid'(_).
%(the T E) casts through the unknown type: what E's type leaves open, a rigid
%type or which alternative of a union, is checked at runtime.
forget_open(T, U) :- ( rigid(T) ; nonvar(T), T = [B|_], B == '|' ), !, U = '%Undefined%'.
forget_open(T, U) :- is_list(T), !, maplist(forget_open, T, U).
forget_open(T, T).
%What a runtime check can test of T: a type variable, rigid or not, is unknown
%there, so (List $a) is checked as a list and a rigid result type is trusted:
checkable(T, C) :- ( var(T) ; rigid(T) ), !, C = '%Undefined%'.
checkable(T, C) :- is_list(T), !, maplist(checkable, T, C).
checkable(T, T).
closed(T) :- checkable(T, C), C =@= T.

%%% Boundaries %%%

%type_boundary(Ctx, V, T, Goals): what passing value V where T is required needs.
type_boundary(_, _, T, []) :- ( var(T) ; wildcard(T) ; type_flag('--no-type-checks') ), !.
type_boundary(Ctx, V, T, Gs) :- static_type(V, S0), ( Ctx = the(_) -> forget_open(S0, S) ; S = S0 ),
                                boundary(Ctx, V, S, T, Gs).
boundary(_, V, S, T, Gs) :- checkable(T, C), ( established(S, C) ; ground(V), typecheck_ok(V, C) ), !,
                            ( type_flag('--oracle'), \+ wildcard(C) -> guard(V, C, G), Gs = [G] ; Gs = [] ).
boundary(_, V, S, T, _) :- conflict(S, T), !,
                           ( ground(V), \+ rigid(S) -> throw(error(literal_type_mismatch(V, T), typecheck))
                                                     ; throw(error(type_conflict(existing(S), required(T)), typecheck)) ).
boundary(native, _, _, _, []) :- !.                    %a native builtin tests its own arguments
boundary(_, _, _, T, []) :- checkable(T, C), wildcard(C), !.
boundary(Ctx, V, _, T, [G]) :- checkable(T, C), guard(V, C, G),
                                 ( type_flag('--warn-runtime-checks')
                                   -> ( nb_current('$compiling', F), F \== none -> true ; F = 'a runnable' ),
                                      format(user_error, "Warning: runtime type check of ~w against ~p in ~w~n", [Ctx, T, F])
                                    ; true ).

%The arguments of a call against a fresh declaration instance:
type_boundary_args(Ctx, Vs, Ts, Goals) :- instantiate(Vs, Ts), maplist(type_boundary(Ctx), Vs, Ts, Gss), append(Gss, Goals).

%type_call(Fun, AVs, Out, Checks, Extra, Type): a call of Fun with the argument
%values AVs needs Checks before it and Extra after it, and has the result Type.
type_call(Fun, AVs, Out, Checks, Extra, Type) :-
        length(AVs, N), ( native_builtin(Fun) -> Ctx = native ; Ctx = Fun ),
        findall(d(As, O), type_decl(Fun, N, As, O, _), Ds),
        ( Ds = [d(As, O)] -> type_boundary_args(Ctx, AVs, As, Checks), result_static_type(Ctx, As, O, Type),
                             %a foreign function's primitive result is checked, not trusted:
                             ( foreign(Fun), primitive(Type) -> type_boundary(foreign(Fun), Out, Type, Extra) ; Extra = [] )
        ; Ds = [_, _|_] -> type_overload(Ctx, Fun, AVs, Out, Ds, Checks, Extra, Type)
        %a partial application checks the arguments it is given:
        ; Arity is N + 1, \+ arity(Fun, Arity),
          findall(As, ( type_decl(Fun, M, As0, _, _), M > N, length(As, N), append(As, _, As0) ), [As])
          -> type_boundary_args(Ctx, AVs, As, Checks), Extra = [], Type = '%Undefined%'
        %cons builds a list of the type that the head and the tail's elements agree on:
        ; memberchk(Fun, [cons, 'cons-atom']), AVs = [H, Tl], static_type(Tl, TT), list_type(TT, E0)
          -> Checks = [], Extra = [], static_type(H, S), ( agreed_type([S, E0], E) -> Type = ['List', E] ; Type = ['List', '%Undefined%'] )
        ; Checks = [], Extra = [], Type = '%Undefined%' ).

%A call of a closure whose arrow type is known is checked against it:
type_closure_call(F, AVs, Checks, Type) :-
        static_type(F, K), nonvar(K), K = [A|_], A == '->', copy_term(K, [_|Ts]),
        length(AVs, NA), length(Ts, NT), NT > NA, !,
        length(ATs, NA), append(ATs, Rest, Ts), ( Rest = [RT] -> true ; RT = ['->'|Rest] ),
        type_boundary_args(closure, AVs, ATs, Checks), result_static_type(closure, ATs, RT, Type).
type_closure_call(_, _, [], '%Undefined%').

%Several declarations of Fun: those the arguments may fit are tried in order
%at runtime, and the result must fit one that accepted the arguments.
type_overload(_, _, _, _, _, [], [], '%Undefined%') :- type_flag('--no-type-checks'), !.
type_overload(Ctx, Fun, AVs, Out, Ds, Checks, Extra, Type) :-
        include({Ctx, AVs}/[d(As, _)]>>catch(\+ \+ type_boundary_args(Ctx, AVs, As, _), error(_, typecheck), fail), Ds, Fits),
        ( Fits == [] -> throw(error(no_matching_overload(Fun), typecheck)) ; true ),
        maplist(overload_tests(Ctx, AVs, Out), Fits, ArgTests, JointTests, Types),
        merged_type(Types, Type),
        Fits = [d(_, O1)|_],
        test_goal(ArgTests, throw(error(no_matching_overload(Fun), typecheck)), Checks),
        test_goal(JointTests, throw(error(literal_type_mismatch(Out, O1), typecheck)), Extra).
overload_tests(Ctx, AVs, Out, d(As0, O0), ArgTest, JointTest, Type) :-
        copy_term(As0-O0, As-O), instantiate(AVs, As),
        foldl([V, T, G0, G]>>( checkable(T, C), \+ value_established(V, T), \+ wildcard(C) -> and(G0, typecheck_ok(V, C), G) ; G = G0 ),
              AVs, As, true, ArgTest),
        ( checkable(O, OC), \+ wildcard(OC) -> and(ArgTest, typecheck_ok(Out, OC), JointTest) ; JointTest = ArgTest ),
        result_static_type(Ctx, As, O, Type).
%Some alternative must hold, or Else: no goal when one surely does.
test_goal(Alts, _, []) :- memberchk(true, Alts), !.
test_goal(Alts, Else, [( Any -> true ; Else )]) :- foldl([G, A0, A]>>( A0 == fail -> A = G ; A = (A0 ; G) ), Alts, fail, Any).
and(true, G, G) :- !.
and(G0, G, (G0, G)).

%%% Runtime %%%

%A call whose callee is known only at runtime (a closure, reduce) checks the
%known parts of the callee's parameter types here, as a known call site would:
dynamic_boundary(F, Args) :- ( length(Args, N), checked_params(F, N, Ts) -> maplist(typecheck_or_error, Args, Ts) ; true ).

%A runtime check: an inline test of the common case, else the value relation.
guard(V, T, ( Fast -> true ; typecheck_or_error(V, T) )) :- fast_test(V, T, Fast), !.
guard(V, T, typecheck_or_error(V, T)).
fast_test(V, 'Number', number(V)) :- !.
fast_test(V, 'String', string(V)) :- !.
fast_test(V, 'Bool', ( V == true ; V == false )) :- !.
fast_test(V, T, ( V == [] ; nonvar(V), V = [_|_] )) :- list_type(T, E), wildcard(E), !.
fast_test(V, Ts, ( is_list(V), V = Xs, Test )) :- tuple_type(Ts), length(Ts, N), length(Xs, N),
        foldl([X, T, G0, G]>>( wildcard(T) -> G = G0
                             ; atom(T), \+ primitive(T) -> and(G0, ( X == T -> true ; typecheck_ok(X, T) ), G)
                             ; fast_test(X, T, F) -> and(G0, F, G)
                             ; and(G0, typecheck_ok(X, T), G) ), Xs, Ts, true, Test).

typecheck_or_error(V, T) :- ( typecheck_ok(V, T) -> true ; throw(error(literal_type_mismatch(V, T), typecheck)) ).

%The value relation. An unbound value fits every type: a check describes the
%value as it is, it does not constrain later bindings.
typecheck_ok(V, _) :- var(V), !.
typecheck_ok(_, T) :- var(T), !.
typecheck_ok(V, 'Number') :- !, number(V).
typecheck_ok(V, 'String') :- !, string(V).
typecheck_ok(V, 'Bool') :- !, ( V == true -> true ; V == false ).
typecheck_ok(_, T) :- wildcard(T), !.
typecheck_ok(V, T) :- list_type(T, E), !, ( wildcard(E) -> ( V == [] -> true ; V = [_|_] ) ; list_ok(V, E) ).
typecheck_ok(V, [A|Ts]) :- A == '->', !, length(Ts, N), callable_arity(V, N).
typecheck_ok(V, [U|Ts]) :- U == '|', !, member(T, Ts), typecheck_ok(V, T), !.
typecheck_ok(V, _) :- opaque(V), !.
%A constructor application fits by its declaration, a tuple field by field
%(a type's atom head may be the value's literal tag); anything else as get-type says:
typecheck_ok([C|Fs], T) :- atom(C), is_list(Fs), length(Fs, N), type_decl(C, N, As, O, _),
                           \+ \+ ( O = T, maplist(typecheck_ok, Fs, As) ), !.
typecheck_ok(V, Ts) :- is_list(Ts), is_list(V), same_length(V, Ts),
                       maplist([X, T]>>( X == T, atom(T) -> true ; typecheck_ok(X, T) ), V, Ts), !.
typecheck_ok(V, T) :- \+ \+ ( 'get-type'(V, T) ; 'get-metatype'(V, T) ).
%A foreign value - a Prolog term or blob that is no MeTTa value - cannot be
%inspected: it fits every type that is not primitive, a list or an arrow.
opaque(V) :- compound(V), !, \+ is_list(V), V \= partial(_, _).
opaque(V) :- blob(V, B), B \== text.
%A function or constructor, or a partial application, taking N - 1 more arguments:
callable_arity(F, N) :- atom(F), !, ( arity(F, N) -> true ; M is N - 1, type_decl(F, M, _, _, _) ).
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
%a tuple type headed by the pattern's own tag, or by the first element's type:
bind_pattern([C|Ps], [H|Ts]) :- atom(C), C == H, same_length(Ps, Ts), !, maplist(bind_pattern, Ps, Ts).
bind_pattern(Ps, [H|Ts]) :- is_list(Ps), ( var(H) ; is_list(H) ; rigid(H) ; primitive(H) ; wildcard(H) ),
                            same_length(Ps, [H|Ts]), !, maplist(bind_pattern, Ps, [H|Ts]).
bind_pattern(_, _).

%The variable of map-atom, filter-atom and foldl-atom ranges over the list's elements:
type_element_var(L, X) :- static_type(L, LT), ( list_type(LT, E) -> type_pattern(X, E) ; true ).

%%% Flags %%%

%--warn-runtime-checks reports each runtime check emitted; --oracle emits a
%check even where the compiler established the type, to test that it never
%fails; --no-type-checks compiles every boundary to nothing (what is held and
%what commits still follows the declarations), to test erasure.
type_flag(F) :- current_prolog_flag(argv, Argv), memberchk(F, Argv).
