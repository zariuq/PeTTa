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
% A check of a value with unbound parts holds those parts to the type until
% they are bound (the held checks below), so what a check establishes stays true.

:- module(types, [ note_type_decl/1, forget_type_decl/1, note_function/1, note_foreign/1,     % declarations
                   type_decl/5, dynamic_contract/3, add_builtin_signatures/2, fn_type/4, type_normalize/2,
                   clause_contract/6, type_arg_policy/3, decl_at/5, arrow_params/4, may_hold/1, note_parametricity/4,                                    % compiling a clause
                   static_type/2, set_static_type/2, merge_static_type/2, strip_static_types/1,
                   type_boundary/4, type_call/6, type_closure_call/6,                        % boundaries
                   type_pattern/2, type_element_var/2, newtype_representation/2, space_type/2, space_row/2, space_read_types/2,
                   typecheck_ok/2, typecheck_or_error/2, typecheck_or_error/3, dynamic_call/4, contract_call/5,
                   rethrow_type_error/1, runtime_the/2, runtime_brand/2,
                   held_active/0, held_transport/3, held_restore/1, held_types/2, hold/1,
                   hold_call/4, held_function/1 ]).             % runtime

%%% Declarations %%%

:- dynamic type_decl/5, symbol_type/2, native_builtin/1, foreign/1, dynamic_contract/3,
           get_type_extended/0, classifier_purity/1, type_alias/2, newtype/2, space_type/2, refinement/3.
% type_decl(F, N, ArgTypes, OutType, Det) for each declaration of F with N
% arguments, Det being plain (->), det, semidet or nondet (the other -[..]->
% arrows); symbol_type(S, T) for each (: S T) giving a symbol a type that is not
% an arrow. native_builtin(F): a builtin
% implemented in Prolog, which tests its own arguments. foreign(F): a function
% imported from Prolog, whose results are not trusted. type_alias(N, T) for
% (: N (Alias T)), a name for T; newtype(N, R) for (: N (Newtype R)), a type of
% its own whose values are represented as R's are (see est/2 and consistent/2);
% refinement(N, B, P) for (: N (Refine B P)), the values of B for which the pure
% predicate P gives True;
% space_type(S, Row) for (: S (SpaceOf Row)), a space whose match patterns may
% apply functions (see space_pattern/4 in translator.pl).

%Arrow spellings, giving the determinism the declared function commits to:
arrow('->', plain) :- !.
arrow('-[det]->', det) :- !.
arrow('-[semidet]->', semidet) :- !.
arrow(A, nondet) :- atom(A), sub_atom(A, 0, _, _, '-['), sub_atom(A, _, _, 0, ']->').

%A function type, with nested arrows written -> and _ written %Undefined%:
fn_type(T, ArgTs, Out, Det) :- is_list(T), T = [A|Ts], atom(A), arrow(A, Det), append(As, [O], Ts), !,
                               maplist(type_normalize, As, ArgTs), type_normalize(O, Out).
type_normalize(T, T) :- var(T), !.
type_normalize('_', '%Undefined%') :- !.
type_normalize(T, N) :- atom(T), type_alias(T, N), !.     %an alias is its definition, normalized when declared
type_normalize([A|Ts], ['->'|Ns]) :- atom(A), arrow(A, _), !, maplist(type_normalize, Ts, Ns).
type_normalize(T, N) :- is_list(T), !, maplist(type_normalize, T, N).
type_normalize(T, T).

%Called for every atom added to or removed from &self (a declaration change
%clears the cached field plans of constructors):
note_type_decl(A) :- A = [C|_], C == ':', retractall(constructor_plans_cache(_, _, _)), retractall(name_kind_cache(_, _)),
                     retractall(space_plan_cache(_, _, _)), fail.
note_type_decl([C, N, [K, B0, P]]) :- C == ':', K == 'Refine', atom(N), atom(P), !, type_normalize(B0, B),
                                      retractall(refinement(N, _, _)), assertz(refinement(N, B, P)).
note_type_decl([C, N, [K, T0]]) :- C == ':', atom(N), kind_store(K, P), !, type_normalize(T0, T),
                                   ( K == 'SpaceOf' -> retype_space(N, T) ; true ),
                                   Old =.. [P, N, _], New =.. [P, N, T], retractall(Old), assertz(New).
note_type_decl([C, _, T]) :- C == ':', is_list(T), T = [H|Ts], \+ ( atom(H), arrow(H, _) ),
                             member(A, Ts), atom(A), arrow(A, _), !,
                             throw(error(syntax_error('Arrows are prefix: write (-> A B), not (A -> B)'), _)).
note_type_decl([C, F, T]) :- C == ':', atom(F), fn_type(T, As, O, D), !, length(As, N),
                             ( type_decl(F, N, As2, O2, _), [As2, O2] =@= [As, O] -> true
                             ; ( may_hold(F) -> true ; \+ ( sub_term(A, As-O), A == 'Atom' ) -> true ; assertz(may_hold(F)) ),
                               assertz(type_decl(F, N, As, O, D)), redeclared(F) ).
%F has a declaration that mentions Atom, so a call may hold some argument
%(type_arg_policy/3 decides); for other functions every argument is evaluated:
:- dynamic may_hold/1.
note_type_decl([C, S, T0]) :- C == ':', atom(S), !, type_normalize(T0, T), representation_declaration(S, T),
                              ( symbol_type(S, T1), T1 =@= T -> true ; assertz(symbol_type(S, T)) ).
note_type_decl(_).
%The values of a representation type (Number, String, Bool, a list) are fixed
%by the value relation alone, so a symbol declared with one must be one of them;
%the values of other names are their declared symbols (see typecheck_ok/2):
representation_declaration(S, T) :- ( \+ type_flag('--no-type-checks'), checkable(T, C), representation(C),
                                        \+ typecheck_ok(S, C)
                                      -> throw(error(literal_type_mismatch(S, T), typecheck))
                                       ; true ).
representation(T) :- primitive(T) ; list_type(T, _) ; is_list(T), T = [U|Ts], U == '|', Ts \== [], maplist(representation, Ts).
kind_store('Alias', type_alias).
kind_store('Newtype', newtype).
kind_store('SpaceOf', space_type).
%A head pattern matches the representation of a Newtype parameter, also inside it:
represented(T, R) :- atom(T), newtype(T, R0), !, represented(R0, R).
represented(T, R) :- is_list(T), !, maplist(represented, T, R).
represented(T, T).
%(brand N E) makes E, a value of N's representation, a value of N:
newtype_representation(N, R) :- ( atom(N), newtype(N, R0) -> R = R0 ; R = '%Undefined%' ).
forget_type_decl(A) :- A = [C|_], C == ':', retractall(constructor_plans_cache(_, _, _)), retractall(name_kind_cache(_, _)),
                       retractall(space_plan_cache(_, _, _)), fail.
forget_type_decl([C, N, [K, _, _]]) :- C == ':', K == 'Refine', atom(N), !, retractall(refinement(N, _, _)).
forget_type_decl([C, N, [K, _]]) :- C == ':', atom(N), kind_store(K, P), !, Old =.. [P, N, _], retractall(Old).
forget_type_decl([C, F, T]) :- C == ':', atom(F), fn_type(T, As, O, _), !, length(As, N),
                               forall(( clause(type_decl(F, N, As2, O2, _), true, Ref), [As2, O2] =@= [As, O] ),
                                      erase(Ref)),
                               redeclared(F).
forget_type_decl([C, S, T0]) :- C == ':', atom(S), !, type_normalize(T0, T),
                                forall(( clause(symbol_type(S, T1), true, Ref), T1 =@= T ), erase(Ref)).
forget_type_decl(_).

%A change to F's declarations renews the contract that calls reaching F only at
%runtime check (see dynamic_call/4) and recompiles F's clauses against them:
redeclared(F) :- retractall(dynamic_contract(F, _, _)), retractall(nonparametric(F, _)),
                 forall(( \+ type_flag('--no-type-checks'), distinct(N, decl_arity(F, N)),
                          contract_of(F, N, C) ),
                        assertz(dynamic_contract(F, N, C))),
                 ( translated_from(_, [=, [G|_], _]), G == F
                   -> format(user_error, "Warning: the type declarations of ~w changed after its definition; ~w~n",
                             [F, 'recompiling it']),
                      recompile_function_clauses(F)
                    ; true ).

%Called for every function defined: get-type rules of the program may give any
%value any type, so they open every type name (see consistent/2).
note_function(F) :- retractall(classifier_purity(_)),
                    ( F == 'get-type', \+ get_type_extended -> assertz(get_type_extended) ; true ).
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
                                               ['min-atom','max-atom','size-atom']-[_,'%Undefined%'],
                                               ['is-var','is-ground','is-expr','is-space']-[_,'Bool'],
                                               ['random-int','random-float']-['Number','Number','Number'],
                                               [repr]-[_,'String'],
                                               [empty]-[_] ]),
                              member(F, Fs).
:- forall(builtin_type(F, T), ( fn_type(T, As, O, D), length(As, N),
                                assertz(type_decl(F, N, As, O, D)), assertz(native_builtin(F)) )).
add_builtin_signatures(Space, true) :- forall(builtin_type(F, T), 'add-atom'(Space, [':', F, T], true)).

unique_type_decl(F, N, As, O, D) :- findall(d(As0, O0, D0), type_decl(F, N, As0, O0, D0), [d(As, O, D)]).

%F's declarations as seen by a call with N arguments: those of F/N or, without
%any, a shorter one whose result arrow takes the rest; a function declared
%(-> A (-> B C)) and called with two arguments is (-> A B C) (currying):
decl_at(F, N, As, O, D) :- ( type_decl(F, N, _, _, _) -> type_decl(F, N, As, O, D)
                           ; type_decl(F, K, As0, O0, D), K < N, M is N - K, arrow_params(O0, M, Bs, O),
                             append(As0, Bs, As) ).
%The first M parameter types of a curried arrow type T, and what it returns then:
arrow_params(T, 0, [], T) :- !.
arrow_params(T, M, Bs, O) :- nonvar(T), fn_type(T, Ps, R, _), length(Ps, L),
                             ( L >= M -> length(Bs, M), append(Bs, Rest, Ps),
                                         ( Rest == [] -> O = R ; T = [A|_], append([A|Rest], [R], O) )
                             ; M1 is M - L, arrow_params(R, M1, Bs1, O), append(Ps, Bs1, Bs) ).
decl_arity(F, N) :- type_decl(F, K, _, O, _), ( N = K ; curried_arity(O, K, N) ).
curried_arity(O, K, N) :- nonvar(O), fn_type(O, Ps, R, _), length(Ps, L),
                          ( between(1, L, I), N is K + I ; K1 is K + L, curried_arity(R, K1, N) ).

%The contract of F/N for calls whose callee is known only at runtime: with one
%declaration its parameters (its clauses check its result), with several each
%declaration's parameters and result, since its clauses check neither:
contract_of(F, N, params(Cs)) :- findall(As0, decl_at(F, N, As0, _, _), [As]), !,
                                 maplist(runtime_type, As, Cs), \+ maplist(wildcard, Cs).
contract_of(F, N, overloads(Os)) :- findall(o(Cs, R), ( decl_at(F, N, As, O, _), maplist(runtime_type, As, Cs),
                                                         runtime_type(O, R) ), Os),
                                    \+ forall(member(o(Cs, R), Os), maplist(wildcard, [R|Cs])).

%The contract a clause of F/N is compiled against: of F's declarations, those
%its constant head arguments can fit, instantiated by them. One gives the
%parameter and result types as seen from the body (see body_contract/4) and the
%commitment; several leave the clause unchecked, since each call is checked
%against the declarations its arguments fit; none is an error.
clause_contract(F, N, Args, PTs, OT, Det) :-
    findall(d(As, O, D), decl_at(F, N, As, O, D), Ds),
    include({Args}/[d(As, _, _)]>>( instantiate(Args, As),
                                    \+ ( nth1(I, Args, V), nth1(I, As, T), static_type(V, S),
                                         represented(T, R), conflict(S, R) ) ), Ds, Fits),
    ( Fits = [d(As, O, D)] -> body_contract(As, O, PTs, OT), Det = D
    ; Ds \== [], Fits == [], \+ type_flag('--no-type-checks') -> throw(error(no_matching_overload(F), typecheck))
    ; OT = '%Undefined%', joint_commitment(Fits, Det) ).
%Several declarations fit: the function commits if each of them does, as the
%weakest of them (determinism is the function's, not one overload's):
joint_commitment(Ds, Det) :- Ds \== [], forall(member(d(_, _, D), Ds), memberchk(D, [det, semidet])), !,
                             ( memberchk(d(_, _, semidet), Ds) -> Det = semidet ; Det = det ).
joint_commitment(_, plain).

%Argument positions that every declaration of F/N types Atom stay unevaluated.
%The result is a list of types for translate_args_by_type/4: Atom or unknown.
type_arg_policy(F, N, Ps) :- findall(As, decl_at(F, N, As, _, _), Ass), Ass \== [],
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
%A head argument of the clause being compiled, rebuilt in its body, is the
%argument, of its type and of the type of the pattern it matched:
static_type(V, T) :- compound(V), nb_current('$params', Ps-Ts), nonvar(Ts), nth1(I, Ps, P), P == V, !,
                     nth1(I, Ts, T0), narrowed(V, T0, T).
static_type(V, 'Number') :- number(V), !.
static_type(V, 'String') :- string(V), !.
static_type(V, 'Bool') :- ( V == true ; V == false ), !.
static_type([], ['List', _]) :- !.
%A symbol that is both a function and a declared value has both types, so no one
%static type; the value relation decides it (at compile time, being ground):
static_type(V, T) :- atom(V), ( fun(V) ; type_decl(V, _, _, _, _) ), \+ symbol_type(V, _),
                     callable_type(V, 0, T), !.
static_type(V, T) :- atom(V), !, ( \+ fun(V), \+ type_decl(V, _, _, _, _), findall(T0, symbol_type(V, T0), [T])
                                   -> true ; T = '%Undefined%' ).
static_type(partial(F, Bs), T) :- atom(F), is_list(Bs), length(Bs, K), callable_type(F, K, T), !.
%A constructor application has its declared type, if its fields establish it:
static_type([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N),
                          \+ \+ ( type_decl(C, N, _, O0, _), constructor_result(O0) ), !,
                          ( unique_type_decl(C, N, As, O, _), constructor_result(O), instantiate(Fs, As),
                            maplist(value_established, Fs, As)
                            -> result_static_type(constructor, As, O, T) ; T = '%Undefined%' ).
%Other data is a list of the type its elements agree on, else the tuple of their
%types; but a symbol without a type gives the expression it heads none, as an
%undeclared function gives none to its calls, and an application of a function
%held as data (quoted, say) is an expression whose head's type is unknown:
static_type([X|Xs], T) :- is_list(Xs), atom(X), fun(X), !, maplist(static_type, Xs, Ss), T = ['%Undefined%'|Ss].
static_type([X|Xs], T) :- is_list(Xs), static_type(X, S), \+ ( atom(X), S == '%Undefined%' ), !,
                          maplist(static_type, Xs, Ss),
                          ( agreed_type([S|Ss], E) -> T = ['List', E] ; T = [S|Ss] ).
static_type(_, '%Undefined%').

%A value matched by a constructor pattern has the pattern's type as well
%(occurrence typing): the intersection (& T0 P) establishes what either does.
narrowed([C|Fs], T0, T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N), unique_type_decl(C, N, _, O, _),
                           constructor_result(O), copy_term(O, P), P \=@= T0, !, T = ['&', T0, P].
narrowed(_, T, T).

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
merge_static_type(V, Ts) :- merged_type(Ts, T),
                            ( var(V) -> ( T == '%Undefined%' -> del_attr(V, pt) ; put_attr(V, pt, T) ) ; true ).
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
%A value is established by its static type; if ground, by a check at compile
%time; and data checked against a tuple type element by element, a symbol
%fitting itself as its tag, as in typecheck_ok/2:
value_established(V, T) :- static_type(V, S), established(S, T), !.
value_established(V, T) :- ground(V), acyclic_term(V), closed(T), \+ nominal(T), \+ refined(T), typecheck_ok(V, T), !.
value_established(V, T) :- is_list(V), tuple_type(T), same_length(V, T), maplist(fits_position, V, T).
fits_position(X, T) :- atom(X), X == T, literal_tag(T), ! ; value_established(X, T).
established(S, T) :- \+ \+ ( copy_term(S, S1), est(S1, T) ).
est(S, T) :- var(T), !, T = S.
est(S, T) :- var(S), !, S = T.
est(_, T) :- wildcard(T), !.
est(S, _) :- wildcard(S), !, fail.
est(S, T) :- atom(S), type_alias(S, D), !, est(D, T).     %an alias declared after a use of its name
est(S, T) :- atom(T), type_alias(T, D), !, est(S, D).
est([U|Ss], T) :- U == '|', !, forall(member(S, Ss), est(S, T)).
est([U|Ss], T) :- U == '&', !, member(S, Ss), est(S, T), !.
est(S, [U|Ts]) :- U == '|', !, member(T, Ts), est(S, T), !.
est(S, T) :- atom(S), S \== T, newtype(S, R), !, \+ wildcard(R), est(R, T).
est(S, T) :- atom(S), S \== T, refinement(S, B, _), !, est(B, T).     %a refinement is a subset of its base
est(S, T) :- list_type(S, SE), !, list_type(T, TE), est(SE, TE).
est(S, T) :- list_type(T, TE), !, tuple_type(S), maplist({TE}/[X]>>est(X, TE), S).
est(S, T) :- ( atom(T) ; rigid(T) ), !, S == T.
est(S, T) :- is_list(S), is_list(T), same_length(S, T), maplist(est, S, T).

%Consistency (Siek and Taha), directional where unions are involved (as in
%consistent subtyping): two types are consistent unless they disagree where
%both are known. A variable, a wildcard or a metatype is consistent with
%every type. Every alternative of a union S must be consistent with T (a value
%of S may be any of them: narrow it with the), and some alternative of a union
%T with S. A value of a rigid type is used only at that
%type, while any value may be returned at it (trusted, see TYPES.md). Types
%that are not consistent are a conflict, a type error at compile time.
conflict(S, T) :- \+ consistent(S, T).
consistent(S, T) :- ( var(S) ; var(T) ; unknown(S) ; unknown(T) ), !.
consistent(S, T) :- atom(S), type_alias(S, D), !, consistent(D, T).
consistent(S, T) :- atom(T), type_alias(T, D), !, consistent(S, D).
consistent([U|Ss], T) :- U == '|', !, forall(member(S, Ss), consistent(S, T)).
consistent([U|Ss], T) :- U == '&', !, once(( member(S, Ss), consistent(S, T) )).
consistent(S, [U|Ts]) :- U == '|', !, once(( member(T, Ts), consistent(S, T) )).
consistent(S, T) :- rigid(S), !, S == T.
consistent(_, T) :- rigid(T), !.
consistent(S, T) :- atom(S), refinement(S, B, _), !, consistent(B, T).
consistent(S, T) :- atom(T), refinement(T, B, _), !, consistent(S, B).
consistent(S, T) :- atom(T), newtype(T, _), !, S == T.                 %a value of N is made by (brand N E)
consistent(S, T) :- atom(S), newtype(S, R), !, \+ wildcard(R), consistent(R, T).
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
may_share_values(S, T) :- ( literal_tag(S), symbol_type(S, T) ; literal_tag(T), symbol_type(T, S) ), !.   %a tag and a name declaring it
may_share_values(S, T) :- type_decl(C, N, _, S, _), \+ fun(C), type_decl(C, N, _, T, _), !.
open_type_name(T) :- get_type_extended, \+ primitive(T), classifier_results(Rs), ( Rs == all -> true ; memberchk(T, Rs) ).
%A get-type rule opens only the names it can return: one whose results are all
%literal names opens those names, one with a computed result every name (known
%again after each change of the get-type equations):
:- dynamic classifier_results_cache/1.
classifier_results(Rs) :- ( classifier_results_cache(Rs) -> true
                          ; findall(B, ( user:translated_from(_, [E, [GT|_], B]), E == '=', GT == 'get-type' ), Bs),
                            ( foldl(result_names, Bs, [], Ns) -> Rs = Ns ; Rs = all ),
                            assertz(classifier_results_cache(Rs)) ).
:- multifile user:metta_on_function_changed/1, user:metta_on_function_removed/1.
user:metta_on_function_changed(F) :- F == 'get-type', retractall(types:classifier_results_cache(_)), retractall(types:name_kind_cache(_, _)).
user:metta_on_function_removed(F) :- F == 'get-type', retractall(types:classifier_results_cache(_)), retractall(types:name_kind_cache(_, _)).
user:metta_on_function_changed(_) :- retractall(types:classifier_purity(_)).   %a definition reachable from a rule
result_names(B, Ns0, Ns) :- atom(B), !, ( memberchk(B, Ns0) -> Ns = Ns0 ; Ns = [B|Ns0] ).
result_names([H|As], Ns0, Ns) :- atom(H), result_positions(H, As, Rs), !, foldl(result_names, Rs, Ns0, Ns).
result_positions(if, [_, A, B], [A, B]).
result_positions(if, [_, A], [A]).
result_positions(case, [_, Cs], Rs) :- is_list(Cs), findall(R, member([_, R], Cs), Rs).
result_positions(let, [_, _, B], [B]).
result_positions('let*', [_, B], [B]).
result_positions(chain, [_, _, B], [B]).
result_positions(progn, As, [L]) :- last(As, L).
result_positions(catch, [E], [E]).
result_positions(superpose, [As], As) :- is_list(As).
result_positions(empty, [], []).
%An atom in a type that names no declared type - no symbol or constructor is
%declared with it, nor is it a kind - is a literal tag, whose one value is the
%symbol itself, as the head of (STV Number) is STV:
literal_tag(T) :- atom(T), \+ primitive(T), \+ wildcard(T), \+ memberchk(T, ['Symbol', 'Grounded', 'Variable', 'Type']),
                  \+ symbol_type(T, 'Type'),
                  \+ symbol_type(_, T), \+ ( type_decl(C, _, _, T, _), \+ fun(C) ),
                  \+ newtype(T, _), \+ type_alias(T, _), \+ refinement(T, _, _), \+ ( symbol_type(T, K), nonvar(K), K = [F|_], F == 'Foreign' ).
%A tuple type may be that of an application of one of a name's constructors:
constructed(Name, _) :- primitive(Name), !, fail.            %no expression is a Number, String or Bool
constructed(Name, [C|Fs]) :- tuple_type([C|Fs]),
                             ( var(C) ; unknown(C) ; length(Fs, N), type_decl(C, N, _, O, _), O == Name ), !.

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

%A function's own declaration as seen from its body: a type variable that is a
%parameter's whole type, or the element type of a list parameter, is the
%caller's choice, a rigid type that equals only itself (the body is parametric
%in it); a variable inside a structured parameter type names an unknown part of
%it, and one that only the result mentions is the function's own choice: both
%are unknown.
body_contract(As, O, PTs, OT) :- copy_term(As-O, PTs-OT),
                                 include([T]>>( var(T) ; list_type(T, E), var(E) ), PTs, Whole),
                                 term_variables(Whole, Rs),
                                 foldl([V, I, J]>>( V = '$rigid'(I), J is I + 1 ), Rs, 1, _),
                                 term_variables(PTs-OT, Ws), maplist(=('%Undefined%'), Ws).
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
%What a runtime check of T tests: nothing (%Undefined%) when every value fits it
%at runtime, as a Newtype over Atom does:
runtime_type(T, C) :- checkable(T, C0), rplan(C0, C).
%A Newtype is nominal: inspecting a value cannot make it one, only (brand N E):
nominal(T) :- sub_term(N, T), atom(N), newtype(N, _), !.
%A refinement's predicate is user code, which runs at runtime only:
refined(T) :- sub_term(N, T), atom(N), refinement(N, _, _), !.

%%% Boundaries %%%

%type_boundary(Ctx, V, T, Goals): what passing value V where T is required needs.
%An argument's T is the declaration instance the call's arguments chose; its
%runtime check tests the declared type K, whose type variables are unknown
%there (TYPES.md §5), so one argument's value never decides another's check.
type_boundary(Ctx, V, T, Gs) :- type_boundary(Ctx, V, T, T, Gs).
type_boundary(_, _, T, _, []) :- ( var(T) ; wildcard(T) ; type_flag('--no-type-checks') ), !.
type_boundary(Ctx, V, T, K, Gs) :- static_type(V, S0), ( Ctx = the(_) -> forget_open(S0, S) ; S = S0 ),
                                   boundary(Ctx, V, S, T, K, Gs).
boundary(_, V, _, T, _, Gs) :- checkable(T, C), value_established(V, C), !,
                            ( type_flag('--oracle'), \+ wildcard(C) -> guard(V, C, G), Gs = [G] ; Gs = [] ).
boundary(_, V, S, T, _, _) :- conflict(S, T), !,
                           ( ground(V), \+ rigid(S) -> throw(error(literal_type_mismatch(V, T), typecheck))
                                                     ; throw(error(type_conflict(existing(S), required(T)), typecheck)) ).
boundary(native, _, _, _, _, []) :- !.                 %a native builtin tests its own arguments
boundary(_, _, _, _, K, []) :- checkable(K, C), rplan(C, P), wildcard(P), !.
boundary(Ctx, V, _, T, K, [G]) :- checkable(K, C0), rplan(C0, C), guard(V, C, C0, G),
                                 ( type_flag('--warn-runtime-checks')
                                   -> ( nb_current('$compiling', F), F \== none -> true ; F = 'a runnable' ),
                                      format(user_error, "Warning: runtime type check of ~w against ~p in ~w~n", [Ctx, T, F])
                                    ; true ).

%The arguments of a call against a fresh declaration instance:
type_boundary_args(Ctx, Vs, Ts, Goals) :- copy_term(Ts, Ks), instantiate(Vs, Ts),
                                          maplist(type_boundary(Ctx), Vs, Ts, Ks, Gss), append(Gss, Goals).

%type_call(Fun, AVs, Out, Checks, Extra, Type): a call of Fun with the argument
%values AVs needs Checks before it and Extra after it, and has the result Type.
type_call(Fun, AVs, Out, Checks, Extra, Type) :-
        length(AVs, N), ( native_builtin(Fun) -> Ctx = native ; Ctx = Fun ),
        findall(d(As, O), decl_at(Fun, N, As, O, _), Ds),
        ( Ds = [d(As, O)] -> copy_term(O, O0), type_boundary_args(Ctx, AVs, As, Checks),
                             result_static_type(Ctx, As, O0, Plain), result_static_type(Ctx, As, O, Inst),
                             ( Inst =@= Plain -> T0 = Plain ; result_trusted(Ctx, Fun, N, O0) -> T0 = Inst ; T0 = Plain ),
                             builtin_result_type(Fun, AVs, T0, Type),
                             %a foreign function's primitive result is checked, not trusted:
                             ( foreign(Fun), primitive(Type) -> type_boundary(foreign(Fun), Out, Type, Extra) ; Extra = [] )
        ; Ds = [_, _|_] -> type_overload(Ctx, Fun, AVs, Out, Ds, Checks, Extra, Type)
        %a partial application checks the arguments it is given:
        ; Arity is N + 1, \+ arity(Fun, Arity),
          findall(As, ( type_decl(Fun, M, As0, _, _), M > N, length(As, N), append(As, _, As0) ), [As])
          -> type_boundary_args(Ctx, AVs, As, Checks), Extra = [], Type = '%Undefined%'
        %a row read from a space declared (SpaceOf Row) is of type Row:
        ; Fun == 'get-atoms', AVs = [S], atom(S), space_type(S, Row) -> Checks = [], Extra = [], copy_term(Row, Type)
        %cons builds a list of the type that the head and the tail's elements agree on:
        ; memberchk(Fun, [cons, 'cons-atom']), AVs = [H, Tl], static_type(Tl, TT), list_type(TT, E0)
          -> Checks = [], Extra = [], static_type(H, S),
             ( agreed_type([S, E0], E) -> Type = ['List', E] ; Type = ['List', '%Undefined%'] )
        ; Checks = [], Extra = [], Type = '%Undefined%' ).

%size-atom, min-atom and max-atom return () for a value that is not a list,
%and min/max a list's own element: their result is a Number only when the
%argument is known to be a list (of Numbers, for min and max).
builtin_result_type(F, [V], _, 'Number') :-
    ( F == 'size-atom' -> E = '%Undefined%' ; memberchk(F, ['min-atom','max-atom']), E = 'Number' ),
    static_type(V, S), established(S, ['List', E]), !.
builtin_result_type(_, _, T, T).

%A call of a closure whose arrow type is known is checked against it. The
%closure is known only at runtime, and its arrow type was checked as its arity
%alone, so its result is checked here (Extra) before it has the declared type:
type_closure_call(F, AVs, Out, Checks, Extra, Type) :-
        static_type(F, K), nonvar(K), K = [A|_], A == '->', copy_term(K, [_|Ts]),
        length(AVs, NA), length(Ts, NT), NT > NA, !,
        length(ATs, NA), append(ATs, Rest, Ts), ( Rest = [RT] -> true ; RT = ['->'|Rest] ),
        type_boundary_args(closure, AVs, ATs, Checks), result_static_type(closure, ATs, RT, Type),
        type_boundary(closure_result, Out, Type, Extra).
type_closure_call(_, _, _, [], [], '%Undefined%').

%Parametric trust (TYPES.md §5): a function's result at a type variable is of the type
%its arguments instantiate only if no clause of the function returns a value of
%unknown type there. A caller that relies on it is recorded, and compiled again
%if a clause found later breaks it (before the next runnable, or once an
%equation added at runtime is in place); a runnable relies only on the clauses
%it sees.
:- dynamic nonparametric/2, trusted_result/3, stale_trust/1.
result_trusted(Ctx, _, _, O0) :- ( Ctx == native ; term_variables(O0, []) ), !.
result_trusted(_, F, N, _) :- \+ nonparametric(F, N),
        ( nb_current('$compiling', C0), C0 \== none
          -> ( user:ho_specialization(B, C0) -> C = B ; C = C0 ),     %a specialized copy goes with its base
             ( trusted_result(F, N, C) -> true ; assertz(trusted_result(F, N, C)) )
        ; A is N + 1, functor(H, F, A), predicate_property(user:H, number_of_clauses(K)), K > 0 ).
%A clause of F/N whose declared result mentions type variables is parametric
%when each is rigid in the body (a parameter's whole type or a list parameter's
%element type) and the answer's static type carries them where the result does:
note_parametricity(F, N, Out, OT) :-
        ( atom(F), \+ type_flag('--no-type-checks'), findall(As-O, decl_at(F, N, As, O, _), [As-O]),
          term_variables(O, OVs), OVs \== [],
          \+ ( maplist(rigid_in(As), OVs), static_type(Out, S), rigid_established(S, OT) )
          -> mark_nonparametric(F, N) ; true ).
rigid_in(As, V) :- member(A, As), ( A == V ; list_type(A, E), E == V ), !.
rigid_established(S, T) :- rigid(T), !, S == T.
rigid_established(_, T) :- \+ ( sub_term(X, T), rigid(X) ), !.
rigid_established(S, T) :- is_list(T), is_list(S), same_length(S, T), maplist(rigid_established, S, T).
mark_nonparametric(F, N) :- ( nonparametric(F, N) -> true
                            ; assertz(nonparametric(F, N)),
                              forall(retract(trusted_result(F, N, C)), ( stale_trust(C) -> true ; assertz(stale_trust(C)) )) ).
recompile_stale :- ( retract(stale_trust(C)) -> user:recompile_function_clauses(C), recompile_stale ; true ).
:- multifile user:metta_on_definitions_settled/0.
user:metta_on_definitions_settled :- types:recompile_stale.
%The result of a constructor application is a declared name, or a name applied
%to types ((Maybe $a)); a declaration without equations whose result is a type
%variable, a primitive, a list, an arrow or a union declares no constructor:
constructor_result(O) :- nonvar(O), \+ primitive(O), \+ wildcard(O), \+ list_type(O, _),
                         \+ ( O = [A|_], atom(A), ( arrow(A, _) ; A == '|' ) ).

%Several declarations of Fun: those the arguments may fit are tried in order
%at runtime, and the result must fit one that accepted the arguments.
type_overload(_, _, _, _, _, [], [], '%Undefined%') :- type_flag('--no-type-checks'), !.
type_overload(Ctx, Fun, AVs, Out, Ds, Checks, Extra, Type) :-
        include({Ctx, AVs}/[d(As, _)]>>catch(\+ \+ type_boundary_args(Ctx, AVs, As, _), error(_, typecheck), fail),
                Ds, Fits),
        ( Fits == [] -> throw(error(no_matching_overload(Fun), typecheck)) ; true ),
        maplist(overload_tests(Ctx, AVs), Fits, ArgTests, Os, Types),
        merged_type(Types, Type),
        test_goal(ArgTests, throw(error(no_matching_overload(Fun), typecheck)), Checks),
        %one admitted alternative: its result type alone, as a guard; several: held jointly
        ( Os = [o(_, RC)] -> ( wildcard(RC) -> Extra = [] ; guard(Out, RC, G), Extra = [G] )
        ; Extra = [hold_call(Fun, AVs, Out, Os)] ).
%An alternative is tested at runtime against its declared types, their type
%variables unknown (one argument never decides another's check); its result
%evidence is the declared schema's, not an instance's:
overload_tests(Ctx, AVs, d(As0, O0), ArgTest, o(Cs, RC), Type) :-
        maplist(runtime_type, As0, Cs), runtime_type(O0, RC),
        foldl([V, C, G0, G]>>( ( wildcard(C) ; value_established(V, C) ) -> G = G0 ; and(G0, typecheck_ok(V, C), G) ),
              AVs, Cs, true, ArgTest),
        result_static_type(Ctx, As0, O0, Type).
%Some alternative must hold, or Else: no goal when one surely does.
test_goal(Alts, _, []) :- memberchk(true, Alts), !.
test_goal(Alts, Else, [( Any -> true ; Else )]) :- foldl([G, A0, A]>>( A0 == fail -> A = G ; A = (A0 ; G) ), Alts, fail, Any).
and(true, G, G) :- !.
and(G0, G, (G0, G)).

%A runtime check: an inline test of the common case, else the value relation.
%A check against a plan names the declared type D when it fails:
guard(V, T, G) :- guard(V, T, T, G).
guard(V, T, D, ( Fast -> true ; Check )) :- fast_test(V, T, Fast), !, check_goal(V, T, D, Check).
guard(V, T, D, Check) :- check_goal(V, T, D, Check).
check_goal(V, T, D, G) :- ( T == D -> G = typecheck_or_error(V, T) ; G = typecheck_or_error(V, T, D) ).
fast_test(V, 'Number', number(V)) :- !.
fast_test(V, 'String', string(V)) :- !.
fast_test(V, 'Bool', ( V == true ; V == false )) :- !.
fast_test(V, T, is_list(V)) :- list_type(T, E), wildcard(E), !.
fast_test(V, Ts, ( is_list(V), V = Xs, Test )) :- tuple_type(Ts), length(Ts, N), length(Xs, N),
        foldl([X, T, G0, G]>>( wildcard(T) -> G = G0
                             ; literal_tag(T) -> and(G0, X == T, G)
                             ; fast_test(X, T, F) -> and(G0, F, G)
                             ; and(G0, ( ground(X), typecheck_ok(X, T) ), G) ), Xs, Ts, true, Test).

%%% Runtime: contracts, the value relation and held checks (types_runtime.pl) %%%

:- include(types_runtime).

%%% Patterns %%%

%The variables of a pattern matched against a value of type T get the types
%that T gives them; nothing is learned where T says nothing.
type_pattern(P, T) :- copy_term(T, T1), bind_pattern(P, T1).
bind_pattern(P, T) :- var(P), !, ( get_attr(P, pt, _) -> true ; set_static_type(P, T) ).
bind_pattern(_, T) :- ( var(T) ; wildcard(T) ), !.
bind_pattern(P, T) :- list_type(T, E), !, ( P = [H|R] -> bind_pattern(H, E), bind_pattern(R, T) ; true ).
bind_pattern([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N), unique_type_decl(C, N, As, O, _),
                           constructor_result(O), O = T, !, maplist(bind_pattern, Fs, As).
%a tuple type headed by the pattern's own tag, or by the first element's type:
bind_pattern([C|Ps], [H|Ts]) :- atom(C), C == H, same_length(Ps, Ts), !, maplist(bind_pattern, Ps, Ts).
bind_pattern(Ps, [H|Ts]) :- is_list(Ps), ( var(H) ; is_list(H) ; rigid(H) ; \+ literal_tag(H) ),
                            \+ arrow_or_union(H), same_length(Ps, [H|Ts]), !, maplist(bind_pattern, Ps, [H|Ts]).
bind_pattern(_, _).
arrow_or_union(H) :- atom(H), ( arrow(H, _) ; H == '|' ; H == 'SpaceOf' ; H == 'List' ), !.

%The variable of map-atom, filter-atom and foldl-atom ranges over the list's elements:
type_element_var(L, X) :- static_type(L, LT), ( list_type(LT, E) -> type_pattern(X, E) ; true ).

%%% Typed spaces %%%

%A space declared (SpaceOf Row) holds rows of Row only: a row added is checked
%against Row and its open parts are held, travelling with the stored row, so
%each row read from the space fits Row (rows written by Prolog code are trusted):
space_row(S, Row) :- ( atom(S), space_type(S, _), \+ type_flag('--no-type-checks')
                       -> space_plan(S, P, T), row_fits(Row, P, T) ; true ).
row_fits(Row, P, T) :- ( fits_held(Row, P) -> true ; type_mismatch(Row, T) ).
:- dynamic space_plan_cache/3.
space_plan(S, P, T) :- ( space_plan_cache(S, P0, T0) -> true
                       ; space_type(S, T0), runtime_type(T0, P0), assertz(space_plan_cache(S, P0, T0)) ), P = P0, T = T0.
%A space declared (SpaceOf Row) after rows were added: they are checked first,
%in order (a row that does not fit rejects the declaration), and stored again,
%so that their open parts are held as well:
retype_space(S, _) :- ( S == '&self' ; type_flag('--no-type-checks') ), !.
retype_space(S, T) :- findall(R, user:'get-atoms'(S, R), Rs),
                      ( Rs == [] -> true
                      ; runtime_type(T, P), maplist({P, T}/[X]>>row_fits(X, P, T), Rs),
                        ( ground(Rs) -> true
                        ; forall(( current_predicate(user:S/A), functor(H, S, A) ), retractall(user:H)),
                          forall(member(R, Rs), user:add_sexp(S, R)) ) ).
%A pattern matched in a space declared (SpaceOf Row) matches rows of Row, so its
%parts have the types of the corresponding parts of Row (see type_pattern/2):
space_read_types(P, Row) :- ( nonvar(P), P = [C|Ps], C == ',' -> maplist({Row}/[Q]>>type_pattern(Q, Row), Ps)
                            ; type_pattern(P, Row) ).

%%% Flags %%%

%--warn-runtime-checks reports each runtime check emitted; --oracle emits a
%check even where the compiler established the type, to test that it never
%fails; --no-type-checks compiles every boundary to nothing (what is held and
%what commits still follows the declarations), to test erasure.
type_flag(F) :- current_prolog_flag(argv, Argv), memberchk(F, Argv).
