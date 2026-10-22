%%%%%%%%%% Determinism modes: an optional check of the arrows' answer counts %%%%%%%%%%
%
% (: f (-[det]-> A B)) says that a call of f has exactly one answer, -[semidet]->
% at most one, -[nondet]-> any number, and -[multi]-> at least one (Mercury's
% determinism categories). The core already commits det and semidet functions
% to their first matching clause; this module checks, when the definitions in
% use are complete (before each runnable and at the end of each file), that
% each body can give no more answers than its arrow allows, and no fewer for
% det and multi. It adds no code to any clause: a program computes the same
% with or without it. The rules are those of AnswerCardinality in Mettapedia's
% ContractTyping/Determinism; this file names them alike.
%
% A grade is a range of answer counts g(Min, Max), Min in 0..1 and Max in
% 0, 1, n: zero g(0,0), one g(1,1), optional g(0,1), nonempty g(1,n), any g(0,n).
% Answers counted are answers when the call returns: termination, exceptions
% and effects are other questions.

:- module(det_modes, ['det-verdict'/2]).
:- use_module(library(apply)).
:- use_module(library(lists)).
:- use_module(library(solution_sequences)).
:- dynamic det_dirty/1, det_inferred/3, det_verdict/3.
%The runtime's own tables (fun/1, arity/2, translated_from/2, match/4, and the
%declarations types.pl exports) are read through user, this module's default
%import module; newtype/2 and symbol_type/2 from types directly.

%%% The grade algebra %%%

declared_grade(det, g(1, 1)).
declared_grade(semidet, g(0, 1)).
declared_grade(multi, g(1, n)).
declared_grade(nondet, g(0, n)).

%seq: G1's answers each continued by G2's; choice: the answers of both;
%join: those of one or the other; once: at most the first.
seq(g(A, B), g(C, D), g(E, F)) :- E is min(A, C), max_mul(B, D, F).
choice(g(A, B), g(C, D), g(E, F)) :- E is max(A, C), max_add(B, D, F).
join(g(A, B), g(C, D), g(E, F)) :- E is min(A, C), max_max(B, D, F).
once_grade(g(A, B), g(A, C)) :- max_max(B, 0, B1), ( B1 == 0 -> C = 0 ; C = 1 ).
refines(g(A, B), g(C, D)) :- A >= C, max_le(B, D).

max_mul(0, _, 0) :- !.
max_mul(_, 0, 0) :- !.
max_mul(1, X, X) :- !.
max_mul(X, 1, X) :- !.
max_mul(n, n, n).
max_add(0, X, X) :- !.
max_add(X, 0, X) :- !.
max_add(_, _, n).
max_max(X, Y, Z) :- ( max_le(X, Y) -> Z = Y ; Z = X ).
max_le(X, X) :- !.
max_le(0, _) :- !.
max_le(1, n).

%%% Inference: grade(Expr, Grade, Sure) %%%
%Sure is false when an unknown callee contributed: a failed check is then
%unproved, not refuted.

grade(V, g(1, 1), true) :- var(V), !.
grade(E, g(1, 1), true) :- \+ is_list(E), !.
grade([], g(1, 1), true) :- !.
grade([H|T], G, S) :- atom(H), form_grade(H, T, G, S), !.
grade([H|T], G, S) :- var(H), !, args_grade(T, GA, SA), closure_grade(H, GC, SC), seq(GA, GC, G), both(SA, SC, S).
grade([H|T], G, S) :- atom(H), fun(H), length(T, N), partial(H, N), !, args_grade(T, G, S).     %a closure, one value
grade([H|T], G, S) :- atom(H), fun(H), !, length(T, N), args_grade_for(H, N, T, GA, SA),
                      callee_grade(H, N, T, GC, SC), seq(GA, GC, G), both(SA, SC, S).
grade(L, G, S) :- args_grade(L, G, S).                         %data: its elements are evaluated

form_grade(quote, _, g(1, 1), true).
form_grade(empty, _, g(0, 0), true).
form_grade(collapse, _, g(1, 1), true).
form_grade(F, _, g(1, 1), true) :- memberchk(F, [foldall, forall, 'map-atom', 'filter-atom', 'foldl-atom']).   %aggregates
form_grade(once, [E], G, S) :- grade(E, G0, S), once_grade(G0, G).
form_grade(superpose, [L], G, S) :- is_list(L), !, choice_all(L, g(0, 0), true, G, S).
form_grade(superpose, _, g(0, n), true).
form_grade(hyperpose, _, g(0, n), true).
form_grade(match, _, g(0, n), true).
form_grade(if, [C, T, E], G, S) :- grade(C, GC, S1), grade(T, GT, S2), grade(E, GE, S3),
                                   join(GT, GE, GB), seq(GC, GB, G), all_sure([S1, S2, S3], S).
form_grade(if, [C, T], G, S) :- grade(C, GC, S1), grade(T, GT, S2), join(GT, g(0, 0), GB), seq(GC, GB, G), both(S1, S2, S).
form_grade(let, [P, V, B], G, S) :- grade(V, GV, S1), grade(B, GB, S2), match_grade(P, V, GP),
                                    seq(GV, GP, G0), seq(G0, GB, G), both(S1, S2, S).
form_grade('let*', [Bs, B], G, S) :- bindings_grade(Bs, g(1, 1), true, GL, SL), grade(B, GB, SB),
                                     seq(GL, GB, G), both(SL, SB, S).
form_grade(case, [K, Bs], G, S) :- grade(K, GK, S1), branches_grade(K, Bs, GB, S2), seq(GK, GB, G), both(S1, S2, S).
form_grade(progn, Es, G, S) :- args_grade(Es, G, S).
form_grade(the, [_, E], G, S) :- grade(E, G, S).
form_grade(brand, [_, E], G, S) :- grade(E, G, S).
form_grade(catch, [E], G, S) :- grade(E, G, S).

%(f a b) with fewer arguments than f takes is a partial application:
partial(F, N) :- N1 is N + 1, \+ arity(F, N1), arity(F, A), A > N1, !.

%A call through a variable: a parameter declared with an arrow has the arrow's
%grade; any other closure may give any number of answers, as far as known.
closure_grade(H, G, true) :- nb_current(det_head, Args-Ts), is_list(Ts), nth1(I, Args, A), A == H, nth1(I, Ts, T),
                             is_list(T), T = [K|_], atom(K), arrow_kind(K, Kind), declared_grade(Kind, G), !.
closure_grade(_, g(0, n), false).

%A pattern matches every value of the value's declared type if it covers that
%type (see covers/2); otherwise it may fail to match:
match_grade(P, _, g(1, 1)) :- var(P), !.
match_grade(P, V, g(1, 1)) :- linear([P]), value_type(V, T), covers([[P]], [T]), !.
match_grade(_, _, g(0, 1)).

%The branches of case: one runs; none may match unless the patterns cover the
%key's declared type:
branches_grade(K, Bs, G, S) :- findall(B, member([_, B], Bs), Bodies), join_all(Bodies, none, true, G0, S),
        ( G0 == none -> G = g(0, 0)
        ; findall([P], ( member([P, _], Bs), linear([P]) ), Rows),
          ( last(Bs, [P, _]), var(P) ; value_type(K, T), covers(Rows, [T]) ) -> G = G0
        ; join(G0, g(0, 0), G) ).

%The declared type of a value: a call's declared result, or a parameter's type:
value_type(V, T) :- var(V), !, nb_current(det_head, Args-Ts), is_list(Ts),
                    nth1(I, Args, A), A == V, nth1(I, Ts, T0), expanded_type(T0, T).
value_type([F|Args], T) :- atom(F), length(Args, N), findall(O, decl_result(F, N, O), [O0]), expanded_type(O0, T).
decl_result(F, N, O) :- match('&self', [':', F, T0], T0, T), is_list(T), T = [A|Ts], atom(A), arrow_kind(A, _),
                        length(Ts, M), N is M - 1, last(Ts, O).

args_grade(Es, G, S) :- seq_all(Es, g(1, 1), true, G, S).
%Arguments held unevaluated (Atom parameters) contribute one answer each:
args_grade_for(F, N, Args, G, S) :- ( type_arg_policy(F, N, Ps) -> true ; length(Ps, N) ),
                                   findall(E, ( nth1(I, Args, E), nth1(I, Ps, P), P \== 'Atom' ), Evaluated),
                                   seq_all(Evaluated, g(1, 1), true, G, S).

%%% Callees %%%

%A declared function has its arrow's grade; an effect-polymorphic arrow
%-[$e]-> the grade of the function passed where its arrow mentions $e:
callee_grade(F, N, Args, G, S) :- findall(D, type_decl_arrow(F, N, D), Ds), Ds \== [], !, decls_grade(Ds, Args, G, S).
callee_grade(F, N, _, G, S) :- builtin_grade(F, N, G), !, S = true.
callee_grade(F, N, _, G, S) :- inferred_grade(F, N, G, S).

decls_grade([D], Args, G, S) :- !, arrow_grade(D, Args, G, S).
decls_grade([D|Ds], Args, G, S) :- arrow_grade(D, Args, G1, S1), decls_grade(Ds, Args, G2, S2),
                                    join(G1, G2, G), both(S1, S2, S).
arrow_grade(d(Kind, _), _, G, true) :- declared_grade(Kind, G), !.
arrow_grade(d(var(E), ArgTs), Args, G, S) :- !,
        ( nth1(I, ArgTs, T), is_list(T), T = [A|_], atom(A), arrow_effect(A, E1), E1 == E,
          nth1(I, Args, Fn), passed_grade(Fn, G0, S0)
          -> G = G0, S = S0 ; G = g(0, n), S = false ).
arrow_grade(d(plain, _), _, g(0, n), false).

%The grade of a function passed as an argument: a name, or a partial application.
passed_grade(F, G, true) :- atom(F), builtin_grade(F, _, G), !.
passed_grade([F|_], G, true) :- atom(F), builtin_grade(F, _, G), !.
passed_grade(F, G, S) :- atom(F), fun(F), !, arity(F, A), N is A - 1, callee_grade(F, N, [], G, S).
passed_grade([F|Bs], G, S) :- atom(F), fun(F), !, arity(F, A), length(Bs, K), N is A - 1, N > K,
                               callee_grade(F, N, Bs, G, S).
passed_grade([L, _, Body], G, S) :- L == '|->', !, grade(Body, G, S).
passed_grade(_, g(0, n), false).

%Each declaration of F/N as d(Kind, ArgTypes), Kind det, semidet, nondet, multi,
%plain (->) or var(E) for -[$e]->; read from the declarations in &self:
type_decl_arrow(F, N, d(Kind, ArgTs)) :- match('&self', [':', F, T0], T0, T), is_list(T), T = [A|Ts], atom(A),
                                         length(Ts, M), N is M - 1, length(ArgTs, N), append(ArgTs, [_], Ts), arrow_kind(A, Kind).
arrow_kind('->', plain) :- !.
arrow_kind('-[det]->', det) :- !.
arrow_kind('-[semidet]->', semidet) :- !.
arrow_kind('-[nondet]->', nondet) :- !.
arrow_kind('-[multi]->', multi) :- !.
arrow_kind(A, var(E)) :- arrow_effect(A, E).
arrow_effect(A, E) :- atom(A), atom_concat('-[', R, A), atom_concat(E, ']->', R), sub_atom(E, 0, 1, _, '$').

%Builtins whose answer counts are fixed:
builtin_grade(F, _, g(1, 1)) :- memberchk(F, ['+', '-', '*', '/', '%', min, max, '<', '>', '<=', '>=', '==', '!=', '=alpha', '=@=',
                                             and, or, not, xor, 'car-atom', 'cdr-atom', 'cons-atom', cons, 'size-atom', repr,
                                             'is-var', 'is-expr', 'is-ground', 'get-state', 'change-state!', 'add-atom',
                                             'remove-atom', 'println!', 'trace!', test, 'new-space', 'new-state', 'bind!',
                                             'map-atom', 'filter-atom', 'foldl-atom', 'get-type', concat, reverse,
                                             'pow-math', 'sqrt-math', 'abs-math', 'floor-math', 'round-math', 'ceil-math',
                                             '=', '=?', '@<', '@>', '<=', '>=', implies, 'first-from-pair', 'second-from-pair',
                                             length, append, 'unique-atom', 'exclude-item', 'is-member', list_to_set, sort,
                                             msort, atom_concat, 'index-atom', 'union-atom', 'intersection-atom',
                                             'subtraction-atom', 'decons-atom', id, 'get-metatype', 'size-atom', 'random-int',
                                             'random-float', 'collapse', 'is-space', 'get-atoms', term_hash, copy_term,
                                             'min-atom', 'max-atom', 'sum-atom', nth0, nth1, last, flatten, sum_list,
                                             max_list, min_list, atom_string, number_string, atom_chars, string_chars,
                                             'format-args', sread, parse, repra]).
builtin_grade(foldall, _, g(1, 1)).
builtin_grade(forall, _, g(1, 1)).

%An undeclared user function: the least grade consistent with its clauses,
%found by iteration from zero over the finite grade lattice (a recursive call
%reads the current approximation):
inferred_grade(F, N, G, S) :- det_inferred(F, N, G-S), !.
inferred_grade(F, N, G, S) :- clause_bodies(F, N, Cs), Cs \== [], !,
        assertz(det_inferred(F, N, g(0, 0)-true)),
        infer_fixpoint(F, N, Cs), det_inferred(F, N, G-S).
inferred_grade(_, _, g(0, n), false).
infer_fixpoint(F, N, Cs) :- det_inferred(F, N, G0-_), clauses_grade(Cs, none, G1, S1),
                            ( G1 == G0 -> retractall(det_inferred(F, N, _)), assertz(det_inferred(F, N, G1-S1))
                            ; retractall(det_inferred(F, N, _)), assertz(det_inferred(F, N, G1-S1)),
                              infer_fixpoint(F, N, Cs) ).

clause_bodies(F, N, Cs) :- findall(c(Args, B), ( translated_from(_, [=, [G|Args], B]), G == F, length(Args, N) ), Cs).

%A clause body is graded knowing its head and its function's parameter types,
%if declared (for calls through a parameter):
clause_grade(c(Args, B), Ts, G, S) :- ( nb_current(det_head, Saved) -> true ; Saved = none ),
        setup_call_cleanup(b_setval(det_head, Args-Ts), grade(B, G, S), b_setval(det_head, Saved)).
param_types(F, N, Ts) :- ( type_decl_arrow(F, N, d(_, Ts0)) -> Ts = Ts0 ; Ts = none ).

%A det or semidet function's answers are those of its first matching clause,
%none if no head matches unless the heads are exhaustive; another function's
%are those of every clause whose head matches.
function_grade(F, N, true, G, S) :- clause_bodies(F, N, Cs), param_types(F, N, Ts), clauses_grade(Cs, Ts, G0, S),
        ( exhaustive(F, N, Cs) -> G = G0 ; join(G0, g(0, 0), G) ).
function_grade(F, N, false, G, S) :- clause_bodies(F, N, Cs), param_types(F, N, Ts),
                                     clauses_choice(Cs, Ts, g(0, 0), true, G, S).
clauses_choice([], _, G, S, G, S).
clauses_choice([C|Cs], Ts, G0, S0, G, S) :- C = c(Args, _), clause_grade(C, Ts, GB0, SB),
        ( all_distinct_vars(Args) -> GB = GB0 ; join(GB0, g(0, 0), GB) ),
        choice(G0, GB, G1), both(S0, SB, S1), clauses_choice(Cs, Ts, G1, S1, G, S).
clauses_grade(Cs, Ts, G, S) :- clauses_join(Cs, Ts, none, true, G2, S), ( G2 == none -> G = g(0, 0) ; G = G2 ).
clauses_join([], _, G, S, G, S).
clauses_join([C|Cs], Ts, G0, S0, G, S) :- clause_grade(C, Ts, GC, SC), ( G0 == none -> G1 = GC ; join(G0, GC, G1) ),
                                          both(S0, SC, S1),
                                          clauses_join(Cs, Ts, G1, S1, G, S).

%Folds of the algebra over lists of expressions:
seq_all([], G, S, G, S).
seq_all([E|Es], G0, S0, G, S) :- grade(E, GE, SE), seq(G0, GE, G1), both(S0, SE, S1), seq_all(Es, G1, S1, G, S).
choice_all([], G, S, G, S).
choice_all([E|Es], G0, S0, G, S) :- grade(E, GE, SE), choice(G0, GE, G1), both(S0, SE, S1), choice_all(Es, G1, S1, G, S).
join_all([], G, S, G, S).
join_all([E|Es], G0, S0, G, S) :- grade(E, GE, SE), ( G0 == none -> G1 = GE ; join(G0, GE, G1) ), both(S0, SE, S1),
                                   join_all(Es, G1, S1, G, S).
bindings_grade([], G, S, G, S).
bindings_grade([[P, V]|Bs], G0, S0, G, S) :- grade(V, GV, SV), match_grade(P, V, GP),
                                             seq(G0, GV, Ga), seq(Ga, GP, G1), both(S0, SV, S1),
                                             bindings_grade(Bs, G1, S1, G, S).

%%% Exhaustiveness of heads (pattern-matrix usefulness, Maranget) %%%
%The heads cover the declared parameter types when no argument vector escapes
%every head. A column whose type has finitely many constructors (a declared
%name, a list, Bool, a tuple, a union of these, a Newtype's representation)
%is split by constructor; any other column is covered by variables only.
%Heads with a repeated variable or a function applied in a pattern constrain
%more than their shape, and are left out (the check stays sound).
exhaustive(_, _, Cs) :- member(c(Args, _), Cs), all_distinct_vars(Args), !.
exhaustive(F, N, Cs) :- type_decl_arrow(F, N, d(_, Ts0)), maplist(expanded_type, Ts0, Ts),
                        findall(Args, ( member(c(Args, _), Cs), linear(Args) ), Rows), covers(Rows, Ts), !.
all_distinct_vars(Args) :- maplist(var, Args), linear(Args).
linear(Args) :- term_variables(Args, Vs), length(Vs, L), occurrences(Args, All), length(All, L).
occurrences(T, Vs) :- ( var(T) -> Vs = [T] ; is_list(T) -> maplist(occurrences, T, Vss), append(Vss, Vs) ; Vs = [] ).
expanded_type(T0, T) :- copy_term(T0, T1), type_normalize(T1, T).

covers(Rows, []) :- !, Rows \== [].
covers(Rows, [_|Ts]) :- \+ ( member([P|_], Rows), nonvar(P) ), !,                %variables only in this column
                        default_rows(Rows, Rows1), covers(Rows1, Ts).
covers(Rows, [T|Ts]) :- constructors(T, Ks), !,
                        forall(member(k(K, FTs), Ks),
                               ( specialize(Rows, K, FTs, Rows1), append(FTs, Ts, Ts1), covers(Rows1, Ts1) )).
covers(Rows, [_|Ts]) :- default_rows(Rows, Rows1), covers(Rows1, Ts).
default_rows(Rows, Rows1) :- findall(Ps, ( member([P|Ps], Rows), var(P) ), Rows1).
specialize(Rows, K, FTs, Rows1) :- findall(Row1, ( member([P|Ps], Rows), pattern_fields(P, K, FTs, Fs),
                                                    append(Fs, Ps, Row1) ), Rows1).
pattern_fields(P, _, FTs, Fs) :- var(P), !, length(FTs, L), length(Fs, L).
pattern_fields([], nil, [], []) :- !.
pattern_fields([C, H, T], cons, _, [H, T]) :- C == cons, !.
pattern_fields(P, sym(S), [], []) :- atom(P), !, P == S.
pattern_fields([C|Fs], con(C1), FTs, Fs) :- atom(C), C == C1, !, same_length(Fs, FTs).
pattern_fields(P, tuple(L), _, P) :- is_list(P), length(P, L), \+ ( P = [C|_], atom(C), fun(C) ).

%The constructors of a type, as k(Constructor, FieldTypes); fails for a type
%with values beyond its declarations (Number, String, an unknown type):
constructors(T, _) :- var(T), !, fail.
constructors(T, [k(nil, []), k(cons, [E, T])]) :- T = [L, E], L == 'List', !.
constructors('Bool', [k(sym(true), []), k(sym(false), [])]) :- !.
constructors([U|Alts], Ks) :- U == '|', !, maplist(constructors, Alts, Kss), append(Kss, Ks).
constructors(T, Ks) :- atom(T), types:newtype(T, R), !, constructors(R, Ks).
constructors(T, Ks) :- atom(T), \+ primitive(T), \+ memberchk(T, ['%Undefined%', 'Atom', 'Expression', 'Symbol']),
                       findall(k(con(C), ATs), ( type_decl(C, _, ATs0, O, _), O == T, \+ fun(C),
                                                 copy_term(ATs0, ATs) ), Cons),
                       findall(k(sym(S), []), types:symbol_type(S, T), Syms),
                       append(Cons, Syms, Ks), Ks \== [], !.
constructors(T, [k(sym(T), [])]) :- types:literal_tag(T), !.                    %a literal tag, its one value
constructors(T, [k(tuple(L), T)]) :- is_list(T), T = [H|_], H \== 'List', H \== '->', \+ ( atom(H), arrow_kind(H, _) ),
                                     length(T, L).
primitive(T) :- memberchk(T, ['Number', 'String', 'Bool']).

both(true, true, true) :- !.
both(_, _, false).
all_sure(L, S) :- ( maplist(==(true), L) -> S = true ; S = false ).

%%% Checking %%%

%A function's arrows, each checked against the inferred grade, and the
%functions its body passes where an arrow's grade is demanded:
check_function(F) :- forall(( distinct(N, ( translated_from(_, [=, [G|Args], _]), G == F, length(Args, N) )),
                              type_decl_arrow(F, N, d(Kind, _)), declared_grade(Kind, D) ),
                            check_arrow(F, N, Kind, D)),
                     forall(distinct(N, ( translated_from(_, [=, [G|Args], _]), G == F, length(Args, N) )),
                            check_passed(F, N)).
check_arrow(F, N, Kind, D) :- ( memberchk(Kind, [det, semidet]) -> Commit = true ; Commit = false ),
        function_grade(F, N, Commit, G, S), verdict(G, S, D, V),
        retractall(det_verdict(F, N, _)), assertz(det_verdict(F, N, V)),
        report(F, N, Kind, V).
%Refuted only when the body surely gives more answers than allowed; fewer
%answers than det or multi need (a head no clause covers, a branch with no
%answer) is unproved, the analysis of exhaustiveness being incomplete:
verdict(G, _, D, proven) :- refines(G, D), !.
verdict(g(A, B), true, g(_, D), refuted(g(A, B))) :- \+ max_le(B, D), !.
verdict(G, _, _, unproved(G)).
report(_, _, _, proven) :- !.
report(F, N, Kind, refuted(G)) :- !, grade_name(G, Name),
        throw(error(determinism_refuted(F/N, Kind, Name), determinism)).
report(F, N, Kind, unproved(G)) :- grade_name(G, Name),
        ( current_prolog_flag(argv, Argv), memberchk('--strict-det', Argv)
          -> throw(error(determinism_unproved(F/N, Kind, Name), determinism))
           ; format(user_error, "Warning: determinism: ~w/~w is declared ~w; its body is ~w as far as known~n",
                    [F, N, Kind, Name]) ).
grade_name(g(0, 0), failure) :- !.
grade_name(g(1, 1), det) :- !.
grade_name(g(0, 1), semidet) :- !.
grade_name(g(1, n), multi) :- !.
grade_name(g(0, n), nondet).

%A function passed to a parameter declared with a det, semidet, multi or nondet
%arrow must have that grade or a finer one, since the callee's grade relies on
%it (closure_grade/3). This is checked for the functions a body passes by name,
%partial application or lambda, and for its own parameters passed on; a
%closure computed at runtime is trusted to keep its declared grade.
check_passed(F, N) :- clause_bodies(F, N, Cs), param_types(F, N, Ts),
        forall(( member(c(Args, B), Cs), call_in(B, Call), Call = [H|As], atom(H), fun(H),
                 length(As, M), type_decl_arrow(H, M, d(_, PTs)),
                 nth1(I, PTs, PT), arrow_grade_of(PT, K, D), nth1(I, As, A) ),
               passed_respects(F, N, Args, Ts, H, A, K, D)).
arrow_grade_of(T, K, D) :- is_list(T), T = [A|_], atom(A), arrow_kind(A, K), declared_grade(K, D).
%The expressions of a body, by elements (a list's tail is no expression), not
%inside quoted data:
call_in(E, E) :- is_list(E), E = [H|_], nonvar(H).
call_in([H|T], C) :- nonvar(H), H \== quote, member(E, [H|T]), nonvar(E), is_list(E), call_in(E, C).
passed_respects(F, N, Args, Ts, H, A, K, D) :- var(A), !,
        ( is_list(Ts), nth1(I, Args, P), P == A, nth1(I, Ts, PT), arrow_grade_of(PT, _, G)
          -> passed_verdict(F, N, H, A, K, D, G, true) ; true ).
passed_respects(F, N, _, Ts, H, A, K, D) :- with_head(none-Ts, passed_grade(A, G, S)), passed_verdict(F, N, H, A, K, D, G, S).
with_head(Ctx, Goal) :- ( nb_current(det_head, Saved) -> true ; Saved = none ),
                        setup_call_cleanup(b_setval(det_head, Ctx), Goal, b_setval(det_head, Saved)).
passed_verdict(_, _, _, _, _, D, G, _) :- refines(G, D), !.
passed_verdict(F, N, H, A, K, _, G, true) :- !, grade_name(G, Name), passed_name(A, AN),
        throw(error(determinism_passed(F/N, AN, Name, H, K), determinism)).
passed_verdict(F, N, H, A, K, _, G, false) :- grade_name(G, Name), passed_name(A, AN),
        format(user_error, "Warning: determinism: ~w/~w passes ~w (~w as far as known) where ~w needs a ~w function~n",
               [F, N, AN, Name, H, K]).
passed_name(A, A) :- atom(A), !.
passed_name([F|_], F) :- atom(F), !.
passed_name(_, 'a closure').

%%% When definitions settle %%%

:- multifile user:metta_on_function_changed/1.
user:metta_on_function_changed(F) :- det_modes:changed(F).
changed(F) :- ( det_dirty(F) -> true ; assertz(det_dirty(F)) ), retractall(det_inferred(_, _, _)).
:- multifile user:metta_on_definitions_settled/0.
user:metta_on_definitions_settled :- det_modes:settle.
settle :- findall(F, retract(det_dirty(F)), Fs0), sort(Fs0, Fs), maplist(check_function, Fs).

%(det-verdict f) gives f's verdicts as (Arity Verdict) for the program to inspect:
'det-verdict'(F, Vs) :- findall([N, V], det_verdict(F, N, V), Vs).

:- multifile prolog:error_message//1.
prolog:error_message(determinism_refuted(F/N, Kind, Inferred)) -->
    [ 'Determinism: ~w/~w is declared ~w, but its body is ~w'-[F, N, Kind, Inferred] ].
prolog:error_message(determinism_passed(F/N, A, Inferred, H, Kind)) -->
    [ 'Determinism: ~w/~w passes ~w (~w) where ~w needs a ~w function'-[F, N, A, Inferred, H, Kind] ].
prolog:error_message(determinism_unproved(F/N, Kind, Inferred)) -->
    [ 'Determinism: ~w/~w is declared ~w; its body is ~w as far as known'-[F, N, Kind, Inferred] ].
