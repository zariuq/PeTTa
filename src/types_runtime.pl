%%%%%%%%%% Types at runtime: contracts of calls reached at runtime, the value %%%%%%%%%%
%%%%%%%%%% relation, and the held checks on open values                     %%%%%%%%%%
%
% Part of module types (included by types.pl): what the code compiled by
% types.pl calls when a value meets a type it was not proven to fit.

%%% Runtime %%%

:- meta_predicate dynamic_call(+, +, ?, 0), contract_call(+, +, +, ?, 0).
%A call whose callee is known only at runtime (a closure, reduce) runs Goal
%under the callee's contract, as a known call site would (type_call/6):
dynamic_call(F, Args, Out, Goal) :- length(Args, N),
                                    ( dynamic_contract(F, N, C) -> contract_call(C, F, Args, Out, Goal) ; call(Goal) ).
contract_call(params(Ts), _, Args, _, Goal) :- maplist(check_param, Args, Ts), call(Goal).
%Several declarations: those the arguments fit admit the call, the body runs
%once, and each answer must fit one of them jointly with the arguments:
contract_call(overloads(Os), F, Args, Out, Goal) :- overload_admit(Os, F, Args), call(Goal), hold_call(F, Args, Out, Os).
check_param(V, T) :- ( T == '%Undefined%' -> true ; typecheck_or_error(V, T) ).
overload_admit(Os, F, Args) :- ( member(o(Ts, _), Os), maplist(fits_now, Args, Ts) -> true
                               ; throw(error(no_matching_overload(F), typecheck)) ).
%The answer Out and the arguments must fit one declaration together now, and
%stay so as their open parts are bound (TYPES.md §4):
hold_call(F, Args, Out, Os) :-
        ( call_fits([Out|Args], Os) -> hold(c([Out|Args], Os, F))
        ; member(o(Ts, R1), Os), maplist(fits_now, Args, Ts) -> type_mismatch(Out, R1)
        ; throw(error(no_matching_overload(F), typecheck)) ).
call_fits(Vs, Os) :- member(o(Ts, R), Os), maplist(fits_now, Vs, [R|Ts]), !.
%(the T V) evaluated at runtime checks what a runtime check can know of T:
runtime_brand(N, V) :- ( type_flag('--no-type-checks') -> true
                        ; newtype_representation(N, R), runtime_type(R, P), typecheck_or_error(V, P) ).
runtime_the(V, T) :- ( type_flag('--no-type-checks') -> true ; runtime_type(T, P), typecheck_or_error(V, P) ).
%reduce turns a failing call into data, but a type error stays an error:
rethrow_type_error(E) :- E = error(_, typecheck), throw(E).

%%% Held checks: constraints on the open parts of checked values %%%
%
%A check of a value with unbound parts adds constraints to a store kept in the
%attribute held of their variables: h(Ts, Rs), Ts the ordered set of types the
%variable must fit once bound, Rs the records it takes part in. A record holds
%one condition on a value: w(V, T), V fits T after every binding (a union or an
%overloaded constructor: one alternative must fit the value as a whole, so its
%parts stay correlated); g(V, T), V fits T once ground (a name that a get-type
%rule may classify); c(Vs, Os, F), the arguments and answer of an overloaded
%call fit one declaration together. Each binding re-tests the constraints of
%its variable and raises at the first that no longer holds; a check never binds
%or fails. Constraints are the checker's own idempotent facts, so the store
%holds each once however often it is checked.
%Checks are against runtime plans (rplan/2), whose unrestricted parts are %Undefined%:
typecheck_or_error(V, T) :- ( ( var(T) ; T == '%Undefined%' ) -> true
                            ; fits_held(V, T) -> true
                            ; type_mismatch(V, T) ).
%The same against a plan P of the declared type D, which a failure names:
typecheck_or_error(V, P, D) :- ( ( var(P) ; P == '%Undefined%' ) -> true
                               ; fits_held(V, P) -> true
                               ; type_mismatch(V, D) ).
%V fits T now, and its open parts are held to what T asks of them:
fits_held(V, T) :- ( atomic(V) -> true ; acyclic_term(V) ), fit_hold(V, T).
%The runtime plan of a type: what a runtime check of it tests, its Newtypes and
%aliases replaced by their representations and every part that all values fit
%by %Undefined%. Compiled checks and contracts use plans, so a check of a type
%that every value fits at runtime (a Newtype over Atom) is never emitted.
rplan(T, P) :- var(T), !, P = '%Undefined%'.
rplan(T, '%Undefined%') :- unrestricted(T), !.
rplan(T, P) :- atom(T), !, ( newtype(T, R) -> rplan(R, P) ; type_alias(T, D) -> rplan(D, P) ; P = T ).
rplan([A|Ts], [A|Ts]) :- ( A == '->' ; A == 'SpaceOf' ), !.
rplan(T, P) :- is_list(T), !, maplist(rplan, T, P).
rplan(T, T).
%Keep the error finite: printing a rational-tree value would not terminate.
type_mismatch(V, T) :- ( acyclic_term(V) -> E = literal_type_mismatch(V, T) ; E = cyclic_type_value(T) ),
                       throw(error(E, typecheck)).
%A rational tree (a cyclic value) fits no type: the check must terminate.
fits_now(V, T) :- ( atomic(V) -> true ; acyclic_term(V) ), typecheck_ok(V, T).
%A type that every value fits at runtime constrains nothing (Newtype Atom too):
unrestricted(T) :- var(T), !.
unrestricted(T) :- wildcard(T), !.
unrestricted(T) :- atom(T), newtype(T, R), !, unrestricted(R).
unrestricted(T) :- atom(T), type_alias(T, D), !, unrestricted(D).
unrestricted([U|Ts]) :- U == '|', member(T, Ts), unrestricted(T), !.

%The constraints that a value fitting T now leaves on its open parts; the
%structure is walked once (a list along its spine):
retain(V, _) :- ground(V), !.
retain(_, T) :- ( var(T) ; T == '%Undefined%' ), !.
retain(V, T) :- var(V), !, add_type(V, T).                            %an open arrow too
retain(V, _) :- opaque(V), !.
retain(V, T) :- list_type(T, E), !, retain_list(V, T, E).
retain(_, [A|_]) :- ( A == '->' ; A == 'SpaceOf' ), !.                %bound: its arity or name is fixed
retain(V, T) :- atom(T), open_type_name(T), !, ( classified_whatever_bound(V, T) -> true ; hold(g(V, T)) ).
%A union: when one alternative fits the value now, it is held to that one;
%when several do, one record keeps the value fitting one of them as a whole:
retain(V, [U|Ts]) :- U == '|', !, include(fits_now(V), Ts, Fit),
                     ( Fit = [T] -> retain(V, T) ; hold(w(V, ['|'|Fit])) ).
retain([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N), constructor_plans(C, N, Ds0),
                     include({T}/[_-O]>>( \+ \+ O = T ), Ds0, Ds), Ds \== [], !,
                     ( Ds = [Ps-O] -> O = T, retain_fields(Fs, Ps)
                     ; hold(w([C|Fs], T)) ).
retain(V, Ts) :- tuple_type(Ts), is_list(V), same_length(V, Ts), !, retain_fields(V, Ts).
retain(V, T) :- hold(g(V, T)).
%A check of a value with open parts in one walk: the value fits T now (as
%typecheck_ok/2 decides) and its open parts are held as retain/2 holds them.
%Lists, unions, a closed name's constructor applications and tuples are walked
%once; any other case, or a walk that fails, is checked and then retained:
fit_hold(V, T) :- ( ground(V) -> typecheck_ok(V, T)
                  ; var(V) -> add_type(V, T)
                  ; fit_walk(V, T) -> true
                  ; typecheck_ok(V, T), retain(V, T) ).
fit_walk(V, T) :- list_type(T, E), !, fit_list(V, T, E).
fit_walk(V, [U|Ts]) :- U == '|', !, include(fits_now(V), Ts, Fit),
                       ( Fit = [A] -> retain(V, A) ; Fit \== [], hold(w(V, ['|'|Fit])) ).
fit_walk(_, [A|_]) :- ( A == '->' ; A == 'SpaceOf' ), !, fail.
fit_walk(V, T) :- atom(T), !, ( name_kind_cache(T, K) -> true ; name_kind(T, K) ), fit_kind(K, T, V).
fit_walk(V, T) :- fit_constructed(V, T, Fit), !, Fit == true.
fit_walk(V, Ts) :- tuple_type(Ts), is_list(V), fit_fields(V, Ts).
fit_kind(any, _, _).
fit_kind(newtype(R), _, V) :- fit_hold(V, R).
fit_kind(alias(D), _, V) :- fit_hold(V, D).
fit_kind(name(false), T, V) :- fit_constructed(V, T, true).
%A constructor application with one declaration whose result can be T: its
%fields are walked (Fit true when they fit); with none, this is no constructor
%of T; with several, the general check decides:
fit_constructed([C|Fs], T, Fit) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N),
                                   ( constructor_plans_cache(C, N, Ds0) -> true ; constructor_plans(C, N, Ds0) ),
                                   include({T}/[_-O]>>( \+ \+ O = T ), Ds0, Ds), Ds \== [],
                                   ( Ds = [Ps-O], O = T, fit_fields(Fs, Ps) -> Fit = true ; Fit = false ).
fit_fields([], []).
fit_fields([X|Xs], [T|Ts]) :- ( ( var(T) ; T == '%Undefined%' ) -> true ; fit_hold(X, T) ), fit_fields(Xs, Ts).
fit_list(V, T, _) :- var(V), !, add_type(V, T).
fit_list([], _, _) :- !.
fit_list([X|Xs], T, E) :- ( ( var(E) ; wildcard(E) ) -> true ; fit_hold(X, E) ), fit_list(Xs, T, E).

%The declarations of a constructor with their field plans (a declaration change
%clears them). A plan keeps the declaration's type variables, which the type the
%application is checked against instantiates (some of (-> $a (Maybe $a)) has a
%Number field at (Maybe Number)):
:- dynamic constructor_plans_cache/3.
constructor_plans(C, N, Ds) :- ( constructor_plans_cache(C, N, Ds) -> true
                               ; findall(Ps-O, ( type_decl(C, N, As, O, _), constructor_result(O), maplist(field_plan, As, Ps) ), Ds),
                                 assertz(constructor_plans_cache(C, N, Ds)) ).
field_plan(T, P) :- ( var(T) -> P = T
                    ; ground(T) -> rplan(T, P)
                    ; is_list(T), T = [A|_], \+ ( atom(A), ( A == '->' ; A == '|' ) ) -> maplist(field_plan, T, P)
                    ; rplan(T, P) ).
retain_list(V, T, _) :- var(V), !, add_type(V, T).                    %an open tail stays a list
retain_list([X|Xs], T, E) :- !, retain(X, E), retain_list(Xs, T, E).
retain_list(_, _, _).
retain_fields([], []).
retain_fields([X|Xs], [T|Ts]) :- ( ( var(T) ; T == '%Undefined%' ) -> true ; atom(X), X == T, literal_tag(T) -> true ; retain(X, T) ),
                                 retain_fields(Xs, Ts).

%A get-type rule that classifies the value without binding any of its open
%parts classifies every instance of it: nothing is left to hold.
classified_whatever_bound(V, T) :- copy_term_nat(V, C), copy_term_nat(V, C0),
                                   \+ \+ ( program_rule_class(C, T), C =@= C0 ).
add_type(W, T) :- note_held,
                  ( get_attr(W, held, h(Ts, Rs)) -> ( ord_memberchk(T, Ts) -> true
                                                    ; ord_add_element(Ts, T, Ts1), put_attr(W, held, h(Ts1, Rs)) )
                  ; put_attr(W, held, h([T], [])) ).
%A record is attached to the variables of its condition, once each:
hold(P) :- note_held, ( held_records -> true ; assertz(held_records) ),
           R = rec(P), term_variables(P, Ws), maplist(attach(R), Ws).
attach(R, W) :- ( get_attr(W, held, h(Ts, Rs)) -> ( has_record(Rs, R) -> true ; put_attr(W, held, h(Ts, [R|Rs])) )
                ; put_attr(W, held, h([], [R])) ).
has_record(Rs, R) :- arg(1, R, P), member(R1, Rs), arg(1, R1, P1), P1 == P, !.
:- dynamic held_active/0, held_records/0, held_function/1. %set at the first held check and record;
%held_function(F): F has an equation added at runtime that restores held checks
note_held :- ( held_active -> true ; assertz(held_active) ).

%A binding of a held variable: to another variable, the two share their
%constraints; to a value, the value is checked, its open parts held, and each
%record re-tested.
held:attr_unify_hook(h(Ts, Rs), Y) :- types:held_bound(Y, Ts, Rs).
held_bound(Y, Ts, Rs) :- var(Y), !,
        ( get_attr(Y, held, h(Ts2, Rs2)) -> ord_union(Ts, Ts2, Ts3), foldl(add_record, Rs, Rs2, Rs3),
                                           put_attr(Y, held, h(Ts3, Rs3))
        ; put_attr(Y, held, h(Ts, Rs)) ).
held_bound(Y, Ts, Rs) :- maplist(check_bound(Y), Ts), maplist(settle, Rs).
check_bound(Y, T) :- ( fits_held(Y, T) -> true ; type_mismatch(Y, T) ).
add_record(R, Rs0, Rs) :- ( has_record(Rs0, R) -> Rs = Rs0 ; Rs = [R|Rs0] ).
settle(R) :- arg(1, R, P),
             ( P == done -> true
             ; \+ condition_holds(P) -> raise_unfit(P)
             ; ground(P) -> setarg(1, R, done)
             ; term_variables(P, Ws), maplist(attach(R), Ws) ).        %its new open variables
condition_holds(w(V, T)) :- fits_now(V, T).
condition_holds(g(V, T)) :- ( ground(V) -> fits_now(V, T) ; true ).
condition_holds(c(Vs, Os, _)) :- call_fits(Vs, Os).
raise_unfit(c(_, _, F)) :- throw(error(no_matching_overload(F), typecheck)).
raise_unfit(P) :- arg(1, P, V), arg(2, P, T), type_mismatch(V, T).

%Held checks travel with every copy PeTTa makes (TYPES.md §3): copy_term/3 gives the
%copy and the goals that restore its constraints. A record whose variables were
%not all copied is dropped: its uncopied variables are unreachable, so nothing
%binds them again and its condition would no longer decide anything.
held:attribute_goals(V, S0, S) :- types:held_goals(V, S0, S).
held_goals(V) --> { get_attr(V, held, h(Ts, Rs)) }, ( { Ts == [] } -> [] ; [types:held_types(V, Ts)] ), record_goals(Rs, V).
record_goals([], _) --> [].
record_goals([R|Rs], V) --> ( { arg(1, R, P), P \== done, term_variables(P, [W|_]), W == V } -> [types:hold(P)] ; [] ),
                            record_goals(Rs, V).
held_types(V, Ts) :- ( var(V) -> maplist(add_type(V), Ts) ; maplist(typecheck_or_error(V), Ts) ).
held_restore(Gs) :- maplist(call, Gs).
held_transport(T, P, Gs) :- copy_term(T, P, Gs0), term_variables(P, Vs), include(kept_goal(Vs), Gs0, Gs).
kept_goal(Vs, types:held_types(V, _)) :- !, var_in(V, Vs).
kept_goal(Vs, types:hold(P)) :- !, term_variables(P, Ws), forall(member(W, Ws), var_in(W, Vs)).
kept_goal(_, _).
var_in(V, Vs) :- member(X, Vs), X == V, !.

%The value relation. An unbound value fits every type: the relation describes
%the value as it is, and typecheck_or_error/2 holds its later binding to the
%type (the held checks above).
typecheck_ok(V, _) :- var(V), !.
typecheck_ok(_, T) :- var(T), !.
typecheck_ok(V, 'Number') :- !, number(V).
typecheck_ok(V, 'String') :- !, string(V).
typecheck_ok(V, 'Bool') :- !, ( V == true -> true ; V == false ).
typecheck_ok(V, T) :- atom(T), !, ( name_kind_cache(T, K) -> true ; name_kind(T, K) ), kind_ok(K, T, V).
typecheck_ok(V, T) :- list_type(T, E), !, list_ok(V, E).
typecheck_ok(V, [A|Ts]) :- A == '->', !, length(Ts, N), callable_arity(V, N).
typecheck_ok(V, [S, _]) :- S == 'SpaceOf', !, atom(V).               %a space is named by its symbol
typecheck_ok(V, [U|Ts]) :- U == '|', !, member(T, Ts), typecheck_ok(V, T), !.
typecheck_ok(V, _) :- opaque(V), !.
%A constructor application fits by its declaration, a tuple field by field
%(a literal tag in the type is matched by the symbol itself); anything else as
%get-type says:
typecheck_ok(V, T) :- constructed_ok(V, T), !.
typecheck_ok(V, Ts) :- is_list(Ts), is_list(V), fields_ok(V, Ts), !.
typecheck_ok(V, T) :- classified(V, T).
%A type named by an atom, by its kind (name_kind/2):
kind_ok(any, _, _).
kind_ok(newtype(R), _, V) :- typecheck_ok(V, R).
kind_ok(refinement(B, P), T, V) :- typecheck_ok(V, B), ( ground(V) -> refine_holds(T, P, V) ; true ).
kind_ok(alias(D), _, V) :- typecheck_ok(V, D).
kind_ok(name(Open), T, V) :- ( constructed_ok(V, T) -> true
                             ; opaque(V) -> true
                             ; V == T, literal_tag(T) -> true          %a tag is its own one value
                             ; ( atomic(V) ; Open == true ; user:nonatomic_declaration ) -> classify(V, T) ).
constructed_ok([C|Fs], T) :- atom(C), \+ fun(C), is_list(Fs), length(Fs, N),
                             ( constructor_plans_cache(C, N, Ds) -> true ; constructor_plans(C, N, Ds) ),
                             ( Ds = [Ps-O] -> true ; member(Ps-O, Ds) ), \+ \+ ( O = T, fields_ok(Fs, Ps) ), !.
%Fields against their plans; an unrestricted or still unknown one fits anything:
fields_ok([], []).
fields_ok([X|Xs], [T|Ts]) :- ( ( var(T) ; T == '%Undefined%' ) -> true ; typecheck_ok(X, T) ), fields_ok(Xs, Ts).
%Else a value fits T as get-type says. An expression can be classified only by
%a declaration of an expression or by a get-type rule that can return T (its
%metatype is Expression); a symbol is looked up as it is:
classified(V, T) :- ( atomic(V) ; user:nonatomic_declaration ; open_type_name(T) ), !, classify(V, T).
classify(V, T) :- ( held_active, \+ ground(V) -> copy_term_nat(V, V1) ; V1 = V ),
                  \+ \+ ( classifier(V1, T) ; 'get-metatype'(V1, T) ).
%What a name is, decided once per change of the declarations and of the get-type
%rules: a wildcard, a Newtype, a refinement, an alias, or a name (declared, or a
%literal tag), open when a get-type rule can return it:
:- dynamic name_kind_cache/2.
name_kind(T, K) :- ( name_kind_cache(T, K0) -> K = K0 ; name_kind_(T, K0), assertz(name_kind_cache(T, K0)), K = K0 ).
name_kind_(T, any) :- wildcard(T), !.
name_kind_(T, newtype(R)) :- newtype(T, R), !.
name_kind_(T, refinement(B, P)) :- refinement(T, B, P), !.
name_kind_(T, alias(D)) :- type_alias(T, D), !.
name_kind_(T, name(Open)) :- ( open_type_name(T) -> Open = true ; Open = false ).
%The program's get-type rules classify values only if no effect is reachable
%from them, so that a check never acts (TYPES.md, erasure); else the builtin
%classification alone:
classifier(V, T) :- value_class(V, T).
classifier(V, T) :- open_type_name(T), classifier_pure, program_rule_class(V, T).   %only names a rule can return
%The builtin classification of a value; an application of a function is an
%unevaluated call, so only a declaration of that very term classifies it:
%The clauses above decide primitives, lists, arrows, tuples and constructor
%applications by structure; what remains is a declaration of the value itself
%(a symbol, or a term declared with (: term T)):
value_class(V, T) :- declared_type(V, T).
%A refinement's predicate: a pure function of one argument giving True (TYPES.md §7);
%an error or another answer means the value does not fit:
refine_holds(N, P, V) :- ( rules_admitted(P) -> true ; throw(error(refinement_predicate(N, P), typecheck)) ),
                         G =.. [P, V, R], catch(G, _, fail), R == true, !.
%The program's own get-type rules (clauses added at runtime, not the builtin one):
program_rule_class(V, T) :- clause('get-type'(V, T), B, R), \+ clause_property(R, file(_)), call(B).
classifier_pure :- ( classifier_purity(P) -> true
                   ; ( rules_admitted('get-type') -> P = true ; P = false ), assertz(classifier_purity(P)),
                     ( P == false -> format(user_error, "Warning: get-type rules that may act are not used by type checks~n", [])
                                   ; true ) ),
                   P == true.
%A type test must only look at its value (TYPES.md §7). A function is admitted when it
%is a pure builtin, or has equations, is not foreign, and everything its
%equations reach is admitted; a call through a variable, an effect form, or a
%builtin not known to be pure is not.
rules_admitted(F) :- equation_bodies(F, Bodies), forall(member(B, Bodies), pure_expr(B, [F])).
admitted(F, Seen) :- memberchk(F, Seen), !.
admitted(F, _) :- pure_builtin(F), !.
admitted(F, Seen) :- \+ foreign(F), equation_bodies(F, Bodies), Bodies \== [], forall(member(B, Bodies), pure_expr(B, [F|Seen])).
equation_bodies(F, Bodies) :- findall(B, ( user:translated_from(_, [E, [G|_], B]), E == '=', G == F ), Bodies).
pure_expr(E, _) :- var(E), !.
pure_expr(E, Seen) :- atomic(E), !, ( atom(E), fun(E) -> admitted(E, Seen) ; true ).    %a function passed as a value
pure_expr([H|_], _) :- var(H), !, fail.                                                %a call through a variable
pure_expr([H|_], _) :- H == quote, !.
pure_expr([H|_], _) :- atom(H), effect_form(H), !, fail.
pure_expr([H, _Pat, V, B], Seen) :- ( H == let ; H == chain ), !, pure_expr(V, Seen), pure_expr(B, Seen).
pure_expr([H, Bs, B], Seen) :- H == 'let*', is_list(Bs), !, forall(member([_, V], Bs), pure_expr(V, Seen)), pure_expr(B, Seen).
pure_expr([H, K, Cs], Seen) :- H == case, is_list(Cs), !, pure_expr(K, Seen), forall(member([_, V], Cs), pure_expr(V, Seen)).
pure_expr([H|As], Seen) :- atom(H), fun(H), !, admitted(H, Seen), forall(member(A, As), pure_expr(A, Seen)).
pure_expr(Xs, Seen) :- is_list(Xs), !, forall(member(X, Xs), pure_expr(X, Seen)).      %data, or a syntax form's parts
pure_expr(_, _).
effect_form(H) :- sub_atom(H, _, 1, 0, '!').                              %by convention, an effect
effect_form(H) :- memberchk(H, ['add-atom', 'remove-atom', match, 'import!', test, hyperpose, with_mutex, transaction,
                                translatePredicate, call, reduce, eval, '|->', forall, foldall, callPredicate,
                                'py-call', 'py-exec', 'py-eval', 'random-int', 'random-float', 'get-state', 'new-state',
                                'bind!', 'new-space', 'get-atoms']).
%Builtins whose results depend only on their arguments:
pure_builtin(F) :- memberchk(F, ['+', '-', '*', '/', '%', min, max, 'pow-math', 'log-math', exp, 'sqrt-math', 'abs-math',
                                 'trunc-math', 'ceil-math', 'floor-math', 'round-math', 'sin-math', 'asin-math', 'cos-math',
                                 'acos-math', 'tan-math', 'atan-math', 'isnan-math', 'isinf-math',
                                 '<', '>', '<=', '>=', '==', '!=', '=', '=?', '=alpha', '=@=', '@<', '@>', '@<=', '@>=',
                                 and, or, xor, implies, not, 'car-atom', 'cdr-atom', 'cons-atom', 'decons-atom', cons, decons,
                                 'size-atom', 'index-atom', 'min-atom', 'max-atom', 'is-member', 'unique-atom', 'union-atom',
                                 'intersection-atom', 'subtraction-atom', member, length, append, reverse, first, last,
                                 'is-var', 'is-ground', 'is-expr', 'is-space', 'get-type', 'get-metatype', repr, id, empty,
                                 if, case, let, 'let*', chain, progn, prog1, catch, superpose, collapse, once, 'and-then',
                                 'or-else', the, brand, data, 'make-list', sort, msort, 'map-atom', 'filter-atom', 'foldl-atom']).

%A foreign value - a Prolog term or blob that is no MeTTa value - cannot be
%inspected: it fits every type that is not primitive, a list or an arrow.
opaque(V) :- compound(V), !, \+ is_list(V), V \= partial(_, _), V \= [_|_].     %a cons cell is a list, possibly open
opaque(V) :- blob(V, B), B \== text.
%A function or constructor, or a partial application, taking N - 1 more arguments:
callable_arity(F, N) :- atom(F), !, ( arity(F, N) -> true ; M is N - 1, type_decl(F, M, _, _, _) ).
callable_arity(partial(F, Bs), N) :- atom(F), length(Bs, K), M is N + K, arity(F, M).
%A list is a finite spine ending in () or in an unbound tail:
list_ok(V, _) :- var(V), !.
list_ok([], _) :- !.
list_ok([X|Xs], T) :- ( wildcard(T) -> true ; typecheck_ok(X, T) ), list_ok(Xs, T).
