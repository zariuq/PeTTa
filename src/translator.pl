:- dynamic translated_from/2.
:- dynamic symbol_use/2.

%Pattern matching, structural and functional/relational constraints on arguments:
constrain_args(X, X, []) :- (var(X); atomic(X)), !.
constrain_args([F, A, B], Out, Goals) :- nonvar(F),
                                         F == cons,
                                         constrain_args(A, A1, G1),
                                         constrain_args(B, B1, G2),
                                         Out = [A1|B1],
                                         append(G1, G2, Goals), !.
constrain_args(Pattern, Var, Goals) :-
                                        functional_pattern_application(Pattern, F, Args), !,
                                        translate_expr([F|Args], GoalsExpr, Var),
                                        flatten(GoalsExpr, Goals).
constrain_args(In, Out, Goals) :- maplist(constrain_args, In, Out, NestedGoalsList),
                                  flatten(NestedGoalsList, Goals), !.

%The single definition of a functional pattern position, matching
%constrain_args/3's dispatch: registered functions elaborate to calls, while
%cons and declaration-only constructors stay literal. Args must be a proper
%list; specialization may produce an open pattern [F|Tail] of no fixed arity.
functional_pattern_application([F|Args], F, Args) :-
    atom(F), F \== cons, fun(F),
    is_list(Args).

%Flatten (= Head Body) MeTTa function into Prolog clauses. A function with one
%declaration has its parameters typed by it and its result checked against it
%(see types.pl); -[det]-> and -[semidet]-> functions commit to the first clause
%whose head matches. A body that returns a partial application returns that
%closure at the function's own arity; a second, saturated clause takes the
%closure's further arguments and calls it at once, as applying it does.
%Mode true elaborates the head's functional patterns, prefix(Gs) gives their goals:
translate_clause(Input, Clauses) :- translate_clause(Input, Clauses, true).
translate_clause(Input, [(Head :- BodyConj)|Saturated], Mode) :-
        Input = [=, [F|Args0], BodyExpr],
        length(Args0, N),
        ( Mode == true -> maplist(constrain_args, Args0, Args1, GoalsA), flatten(GoalsA, GoalsPrefix)
        ; Args1 = Args0, ( Mode = prefix(GoalsPrefix) -> true ; GoalsPrefix = [] ) ),
        ( atom(F), nb_current(F, Prev) -> true ; Prev = [] ),
        copy_term_nat(fun_meta(Args0, Args1, GoalsPrefix, BodyExpr), Meta),
        nb_setval(F, [Meta | Prev]),
        %the contract the clause is compiled against (see types.pl):
        clause_contract(F, N, Args1, PTs, OT, Det),
        with_compiling(F, Args1-PTs,
                       ( ( nonvar(PTs) -> maplist(type_pattern, Args1, PTs) ; true ),
                         translate_declared_body(F, N, BodyExpr, GoalsBody, Out),
                         type_boundary(output(F), Out, OT, OutChecks), note_parametricity(F, N, Out, OT),
                         ( nonvar(Out), Out = partial(Base, Bound), atom(Base)
                           -> ignore(saturated_call(F, Base, Bound, OT, Extra, SatGoals, SatOut)) ; true ) )),
        ( memberchk(Det, [det, semidet]) -> Commit = [!] ; Commit = [] ),
        append(Args1, [Out], FinalArgs),
        Head =.. [F|FinalArgs],
        note_arity(F, FinalArgs),
        append([GoalsPrefix, Commit, GoalsBody, OutChecks], Goals),
        goals_list_to_conj(Goals, BodyConj),
        ( var(Extra) -> Saturated = []
        ; append([Args1, Extra, [SatOut]], SatArgs),
          SatHead =.. [F|SatArgs],
          note_arity(F, SatArgs),
          append([GoalsPrefix, Commit, GoalsBody, SatGoals], SatGs),
          goals_list_to_conj(SatGs, SatBody),
          Saturated = [(SatHead :- SatBody)] ).

%The saturated call of a returned closure partial(Base, Bound): the M further
%arguments the declared result arrow takes (else the fewest Base can take),
%typed by that arrow, and Base called with them as a known call; the
%result is checked against what the arrow returns:
saturated_call(F, Base, Bound, OT, Extra, Goals, Out) :-
        length(Bound, NB),
        findall(M, ( arity(Base, A), M is A - NB - 1, M > 0 ), Ms0), sort(Ms0, Ms),
        ( nonvar(OT), fn_type(OT, Ps, _, _), length(Ps, L), memberchk(L, Ms) -> M = L ; Ms = [M|_] ),
        length(Extra, M),
        ( arrow_params(OT, M, Bs, R) -> maplist(type_pattern, Extra, Bs) ; R = '%Undefined%' ),
        append(Bound, Extra, AVs),
        type_call(Base, AVs, Out, Checks, After, Type),
        build_call_or_partial(Base, AVs, Out, Checks, After, CallGoals),
        set_static_type(Out, Type),
        type_boundary(output(F), Out, R, OutChecks),
        append(CallGoals, OutChecks, Goals).

note_arity(F, Args) :- length(Args, A), ( arity(F, A) -> true ; assertz(arity(F, A)) ).

%Assert an equation's clauses (see translate_clause/3) with How (assertz or
%asserta); a saturated clause is recorded as derived from the equation, so what
%reads the program's equations through translated_from/2 sees each once:
assert_translated(Term, Clauses, Refs) :- assert_translated(assertz, Term, Clauses, Refs).
assert_translated(How, Term, [C|Cs], [R|Rs]) :-
        call(How, C, R), assertz(translated_from(R, Term)),
        maplist({How, Term}/[S, Ref]>>( call(How, S, Ref), assertz(translated_from(Ref, saturated(Term))) ), Cs, Rs).

%A function declared (-> .. Atom) returns its body as data; under the other
%arrows an Atom result is any value, computed by the body:
translate_declared_body(F, N, Expr, [], Expr) :- atom(F), type_decl(F, N, _, Out, plain), Out == 'Atom', !.
translate_declared_body(_, _, Expr, Goals, Out) :- translate_expr(Expr, Goals, Out).

%While F's clause is translated, '$compiling' names F and '$params' holds its
%head arguments with their types (see static_type/2):
with_compiling(F, Params, Goal) :- ( nb_current('$compiling', Prev) -> true ; Prev = none ),
                                   ( nb_current('$params', PrevPs) -> true ; PrevPs = none ),
                                   setup_call_cleanup(( b_setval('$compiling', F), b_setval('$params', Params) ), Goal,
                                                      ( b_setval('$compiling', Prev), b_setval('$params', PrevPs) )).

%Retranslate F's clauses in source order, once they all translate: a type
%declaration arrived late, or a name they used as data became a function.
recompile_function_clauses(F) :- findall(Ref-Term, ( translated_from(Ref, Term), Term = [=, [G|_], _], G == F,
                                                     clause(_, _, Ref) ), Us),
                                 findall(Ref, ( translated_from(Ref, saturated([=, [G|_], _])), G == F ), Ss),
                                 ( Us == [] -> true
                                 ; ( nb_current(F, Metas) -> true ; Metas = [] ),
                                   nb_setval(F, []),
                                   ( catch(maplist([_-Term, Term-Clauses]>>translate_clause(Term, Clauses), Us, TCs), E, true) -> true ; true ),
                                   ( nonvar(TCs), var(E)
                                     -> forall(( member(Ref-_, Us) ; member(Ref, Ss) ), ( retractall(translated_from(Ref, _)), erase(Ref) )),
                                        forall(member(Term-Clauses, TCs), assert_translated(Term, Clauses, _)),
                                        invalidate_specializations(F)
                                      ; nb_setval(F, Metas),
                                        ( nonvar(E) -> throw(E) ; true ) ) ).

%Record atoms compiled as plain symbol heads, so a late function registration
%can be flagged; a declared function's definition may come later, and then the
%clauses that used its name as data are retranslated:
:- dynamic symbol_head/1.
note_symbol_head(HV) :- atom(HV), !,
                        ( symbol_head(HV) -> true ; assertz(symbol_head(HV)) ),
                        ( nb_current('$compiling', F), F \== none, type_decl(HV, _, _, _, _), \+ symbol_use(HV, F)
                          -> assertz(symbol_use(HV, F)) ; true ).
note_symbol_head(_).
late_function(F) :- note_function(F),
                    forall(retract(symbol_use(F, G)), ( G == F -> true ; recompile_function_clauses(G) )).

%Print compiled clause:
maybe_print_compiled_clause(_, _, _) :- silent(true), !.
maybe_print_compiled_clause(Label, FormTerm, Clauses) :- is_list(Clauses), !,
    forall(member(Clause, Clauses), maybe_print_compiled_clause(Label, FormTerm, Clause)).
maybe_print_compiled_clause(Label, FormTerm, Clause) :-
    swrite(FormTerm, FormStr),
    format("\e[33m-->  ~w  -->~n\e[36m~w~n\e[33m--> prolog clause -->~n\e[32m", [Label, FormStr]),
    print_clause(Clause),
    format("\e[33m^^^^^^^^^^^^^^^^^^^^^~n\e[0m").

%Printing a clause must not change the program: portray_clause/2 asks for each
%goal's meta-predicate declaration, which would autoload a library predicate of
%the same name as a function not yet defined (ugraphs' compose/3, say):
print_clause(Clause) :- current_prolog_flag(autoload, A),
                        setup_call_cleanup(set_prolog_flag(autoload, explicit), portray_clause(current_output, Clause),
                                           set_prolog_flag(autoload, A)).

%Conjunction builder, turning goals list to a flat conjunction:
goals_list_to_conj([], true)      :- !.
goals_list_to_conj([G], G)        :- !.
goals_list_to_conj([G|Gs], (G,R)) :- goals_list_to_conj(Gs, R).

resolve_memoization(Fun, Args, Out, Goal) :-
    ( metta_memoized_dispatch_call(Fun, Args, Out, Goal)
    -> true
    ; append(Args, [Out], DirectArgs),
      Goal =.. [Fun|DirectArgs]
    ).
incomplete_application_kind(Fun, Arity, partial) :- ( arity(Fun, KnownArity), KnownArity >= Arity
                                                     ; \+ arity(Fun, _) ), !.
incomplete_application_kind(_, _, overapplied).

throw_function_overapplication(Fun, ActualInputArity) :-
    findall(InputArity, (arity(Fun, Arity), InputArity is Arity - 1), InputArities),
    sort(InputArities, KnownInputArities),
    throw(error(domain_error(function_input_arities(Fun, KnownInputArities), ActualInputArity), none)).

% Runtime dispatcher: call F if it's a registered fun/1, else keep as list:
reduce([F|Args], Out) :- nonvar(F), atom(F), fun(F)
                         -> % --- Case 1: callable predicate ---
                            length(Args, N),
                            Arity is N + 1,
                            ( current_predicate(F/Arity) , \+ (current_op(_, _, F), Arity =< 2)
                              -> resolve_memoization(F, Args, Out, Goal),
                                 catch(dynamic_call(F, Args, Out, Goal), E, rethrow_type_error(E))
                            ; incomplete_application_kind(F, Arity, partial)
                              -> Out = partial(F,Args)
                            ; throw_function_overapplication(F, N) )
                          ; % --- Case 2: partial closure ---
                            compound(F), F = partial(Base, Bound) -> append(Bound, Args, NewArgs),
                                                                     reduce([Base|NewArgs], Out)
                          ; % --- Case 3: leave unevaluated ---
                            Out = [F|Args],
                            \+ cyclic_term(Out).

%Calling reduce from aggregate function foldall needs this argument wrapping
agg_reduce(AF, Acc, Val, NewAcc) :- reduce([AF, Acc, Val], NewAcc).

%Combined expr translation to goals list
translate_expr_to_conj(Input, Conj, Out) :- translate_expr(Input, Goals, Out),
                                            goals_list_to_conj(Goals, Conj).

%Special stream operation rewrite rules before main translation
rewrite_streamops(['trace!', Arg1, Arg2],
                  [progn, ['println!', Arg1], Arg2]).
rewrite_streamops([unique, Arg],
                  [call, [superpose, ['unique-atom', [collapse, Arg]]]]).
rewrite_streamops(['alpha-unique', Arg],
                  [call, [superpose, ['alpha-unique-atom', [collapse, Arg]]]]).
%Only the one-argument standard-library resolver is curated. Two-argument
%library paths can come from git-import!, and ordinary file imports remain
%user-origin.
rewrite_streamops(['import!', Space, [library, Name]],
                  ['library-import!', Space, Name]).
rewrite_streamops([union, [superpose|A], [superpose|B]],
                  [call, [superpose, ['union-atom', [collapse, [superpose|A]],
                                                    [collapse, [superpose|B]]]]]).
rewrite_streamops([intersection, [superpose|A], [superpose|B]],
                  [call, [superpose, ['intersection-atom', [collapse, [superpose|A]],
                                                           [collapse, [superpose|B]]]]]).
rewrite_streamops([subtraction, [superpose|A], [superpose|B]],
                  [call, [superpose, ['subtraction-atom', [collapse, [superpose|A]],
                                                          [collapse, [superpose|B]]]]]).
rewrite_streamops(X, X).

%Guarded stream ops rewrite rule application, successfully avoiding copy_term:
safe_rewrite_streamops(In, Out) :- ( compound(In), In = [Op|_], atom(Op) -> rewrite_streamops(In, Out)
                                                                          ; Out = In).

%Turn MeTTa code S-expression into goals list:
translate_expr(X, [], X)          :- ((var(X) ; atomic(X)) ; X = partial(_,_)), !.
translate_expr([H0|T0], Goals, Out) :-
        safe_rewrite_streamops([H0|T0],[H|T]),
        translate_expr(H, GsH, HV),
        %--- Translator rules ---:
        ( nonvar(HV), translator_rule(HV) -> length(T, NHook),
                                             ( type_arg_policy(HV, NHook, Ps) -> translate_args_by_type(T, Ps, GsT, T1)
                                                                          ; translate_args(T, GsT, T1) ),
                                             append(T1,[Gs],Args),
                                             HookCall =.. [HV|Args],
                                             call(HookCall),
                                             translate_expr(Gs, GsE, Out),
                                             append([GsH,GsT,GsE],Goals)
        %--- Explicit data construction: the fields are evaluated, the head is never called ---:
        ; ( HV == data ; HV == 'make-list' ) -> translate_args(T, GsT, Out),
                                                append(GsH, GsT, Goals)
        %--- Non-determinism ---:
        ; HV == superpose, T = [Args], is_list(Args) -> build_superpose_branches(Args, Out, Branches, Types),
                                                        disj_list(Branches, Disj),
                                                        merge_static_type(Out, Types),
                                                        append(GsH, [Disj], Goals)
        ; HV == collapse, T = [E] -> translate_expr_to_conj(E, Conj, EV),
                                     static_type(EV, ET), set_static_type(Out, ['List', ET]),
                                     append(GsH, [findall(EV, Conj, Out)], Goals)
        ; HV == cut, T = [] -> append(GsH, [(!)], Goals),
                               Out = true
        ; HV == test, T = [Expr, Expected] -> translate_expr_to_conj(Expr, Conj, Val),
                                              translate_expr(Expected, GsE, ExpVal),
                                              Goal1 = ( findall(Val, Conj, Results),
                                                        (Results = [Actual] -> true
                                                                             ; Actual = Results ) ),
                                              append(GsH, [Goal1], G1),
                                              append(G1, GsE, G2),
                                              append(G2, [test(Actual, ExpVal, Out)], Goals)
        %(Conj -> true ; fail) is once(Conj), compiled inline rather than meta-called;
        %the else keeps it once when it is a whole branch of a disjunction (superpose),
        %where a bare (Conj -> true) would read as the condition of an if-then-else:
        ; HV == once, T = [X] -> translate_expr_to_conj(X, Conj, Out),
                                 append(GsH, [(Conj -> true ; fail)], Goals)
        ; HV == hyperpose, T = [L]
          -> ( nonvar(L), is_list(L)
               -> build_hyperpose_branches(L, Branches, Types),
                  merge_static_type(Out, Types),
                  append(GsH, [concurrent_and(member((Goal,Res), Branches), (call(Goal), Out = Res))], Goals)
               ; translate_expr(L, GsL, LV),
                 append(GsH, GsL, Inner),
                 append(Inner, [hyperpose_runtime(LV, Out)], Goals) )
        ; HV == with_mutex, T = [M,X] -> translate_expr_to_conj(X, Conj, Out),
                                         append(GsH, [with_mutex(M,Conj)], Goals)
        ; HV == transaction, T = [X] -> translate_expr_to_conj(X, Conj, Out),
                                        append(GsH, [transaction(Conj)], Goals)
        %--- Sequential execution ---:
        ; HV == progn, T = Exprs -> translate_args(Exprs, GsList, Outs),
                                    append(GsH, GsList, Tmp),
                                    last(Outs, Out),
                                    Goals = Tmp
        ; HV == prog1, T = Exprs -> Exprs = [First|Rest],
                                    translate_expr(First, GsF, Out),
                                    translate_args(Rest, GsRest, _),
                                    append(GsH, GsF, Tmp1),
                                    append(Tmp1, GsRest, Goals)
        %--- Conditionals ---:
        ; HV == if, T = [Cond, Then] -> translate_if_cond(Cond, ConC, CondGoal),
                                        translate_expr_to_conj(Then, ConT, Tv),
                                        static_type(Tv, TT),
                                        build_branch(ConT, Tv, Out, BT),
                                        merge_static_type(Out, [TT]),
                                        ( ConC == true -> append(GsH, [ ( CondGoal -> BT ) ], Goals)
                                                        ; append(GsH, [ ( ConC, ( CondGoal -> BT ) ) ], Goals) )
        ; HV == if, T = [Cond, Then, Else] -> translate_if_cond(Cond, ConC, CondGoal),
                                              translate_expr_to_conj(Then, ConT, Tv),
                                              translate_expr_to_conj(Else, ConE, Ev),
                                              static_type(Tv, TT), static_type(Ev, TE),
                                              build_branch(ConT, Tv, Out, BT),
                                              build_branch(ConE, Ev, Out, BE),
                                              merge_static_type(Out, [TT, TE]),
                                              ( ConC == true -> append(GsH, [ (CondGoal -> BT ; BE) ], Goals)
                                                              ; append(GsH, [ (ConC, (CondGoal -> BT ; BE)) ], Goals) )
        %A case whose arguments do not fit (case Key ((Pattern Value) ...))
        %compiles as a data list - warn, because that is rarely intended and
        %the downstream errors do not mention case at all:
        ; HV == case, \+ ( T = [_, Ps], is_list(Ps), forall(member(Pr, Ps), (is_list(Pr), length(Pr, 2))) )
          -> format(user_error, "Warning: (case ...) does not match (case Key ((Pattern Value) ...)) and compiles as plain data~n", []),
             eval_data_list([HV|T], GsD, Out),
             append(GsH, GsD, Goals)
        ; HV == case, T = [KeyExpr, PairsExpr] -> ( select(Found0, PairsExpr, Rest0),
                                                    subsumes_term(['Empty', _], Found0),
                                                    Found0 = ['Empty', DefaultExpr],
                                                    NormalCases = Rest0
                                                    -> translate_expr_to_conj(KeyExpr, GkConj, Kv),
                                                       translate_case(NormalCases, Kv, Out, CaseGoal, KeyGoal, Types),
                                                       translate_expr_to_conj(DefaultExpr, ConD, DOut),
                                                       static_type(DOut, DT),
                                                       build_branch(ConD, DOut, Out, DefaultThen),
                                                       merge_static_type(Out, [DT|Types]),
                                                       case_with_empty(GkConj, CaseGoal, DefaultThen, Combined),
                                                       append([GsH, KeyGoal, [Combined]], Goals)
                                                     ; translate_expr(KeyExpr, Gk, Kv),
                                                       translate_case(PairsExpr, Kv, Out, IfGoal, KeyGoal, Types),
                                                       merge_static_type(Out, Types),
                                                       append([GsH, Gk, KeyGoal, [IfGoal]], Goals) )
        %--- Short-circuit boolean operators ---:
        ; HV == 'and-then', T = [A, B] -> translate_bool_operand(A, ConjA, Av),
                                           translate_bool_operand(B, ConjB, Bv),
                                           set_static_type(Out, 'Bool'),
                                           append(GsH, [(ConjA, (Av == true -> (ConjB, Out = Bv) ; Out = false))], Goals)
        ; HV == 'or-else', T = [A, B] -> translate_bool_operand(A, ConjA, Av),
                                           translate_bool_operand(B, ConjB, Bv),
                                          set_static_type(Out, 'Bool'),
                                          append(GsH, [(ConjA, (Av == true -> Out = true ; (ConjB, Out = Bv)))], Goals)
        %--- Unification constructs ---:
        ; (HV == let ; HV == chain), T = [Pat, Val, In] -> translate_pattern(Pat, Gp, Pv),
                                                           translate_expr(Val, Gv, V),
                                                           static_type(V, VT), type_pattern(Pv, VT),
                                                           translate_expr(In,  Gi, Out),
                                                           append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
        ; HV == 'let*', T = [Binds, Body] -> letstar_to_rec_let(Binds,Body,RecLet),
                                             translate_expr(RecLet,  Goals, Out)
        ; HV == sealed, T = [Vars, Expr] -> translate_expr_to_conj(Expr, Con, Val),
                                            static_type(Val, VT), set_static_type(Out, VT),
                                            Goals = [copy_term(Vars,[Con,Val],_,[Ncon,Out]),Ncon]
        %--- Iterating over non-deterministic generators without reification ---:
        ; HV == 'forall', T = [GF, TF]
          -> ( is_list(GF) -> GF = [GFH|GFA],
                              translate_expr(GFH, GsGFH, GFHV),
                              route_args(GFHV, GFA, GsGFA, GFAv),
                              append(GsGFH, GsGFA, GsGF),
                              GenList = [GFHV|GFAv]
                            ; translate_expr(GF, GsGF, GFHV),
                              GenList = [GFHV] ),
             translate_expr(TF, GsTF, TFHV),
             TestList = [TFHV, V],
             goals_list_to_conj(GsGF, GPre),
             GenGoal = (GPre, reduce(GenList, V)),
             append(GsH, GsTF, Tmp0),
             set_static_type(Out, 'Bool'),
             append(Tmp0, [( forall(GenGoal, ( reduce(TestList, Truth), Truth == true )) -> Out = true ; Out = false )], Goals)
        ; HV == 'foldall', T = [AF, GF, InitS]
          -> translate_expr_to_conj(InitS, ConjInit, Init),
             translate_expr(AF, GsAF, AFV),
             ( GF = [M|_], (M==match ; M==let ; M=='let*') -> LambdaGF = ['|->', [], GF],
                                                              translate_expr(LambdaGF, GsGF, GFHV),
                                                              GenList = [GFHV]
             ; is_list(GF) -> GF = [GFH|GFA],
                              translate_expr(GFH, GsGFH, GFHV),
                              route_args(GFHV, GFA, GsGFA, GFAv),
                              append(GsGFH, GsGFA, GsGF),
                              GenList = [GFHV|GFAv]
                            ; translate_expr(GF, GsGF, GFHV),
                              GenList = [GFHV] ),
             append(GsH, GsAF, Tmp1),
             append(Tmp1, GsGF, Tmp2),
             static_type(Init, IT), static_type(AFV, AT),
             ( nonvar(AT), AT = [A|ATs], A == '->' -> last(ATs, RT) ; RT = '%Undefined%' ),
             merge_static_type(Out, [IT, RT]),
             append(Tmp2, [ConjInit, foldall(agg_reduce(AFV, V), reduce(GenList, V), Init, Out)], Goals)
        %--- Higher-order functions with pseudo-lambdas and lambdas ---:
        ; HV == 'foldl-atom', T = [List, Init, AccVar, XVar, Body]
          -> translate_expr_to_conj(List, ConjList, L),
             translate_expr_to_conj(Init, ConjInit, InitV),
             type_element_var(L, XVar),
             translate_expr_to_conj(Body, BodyConj, BG),
             static_type(InitV, IT), static_type(BG, BT), merge_static_type(Out, [IT, BT]),
             exclude(==(true), [ConjList, ConjInit], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [foldl([XVar, AccVar, NewAcc]>>(BodyConj, ( number(BG) -> NewAcc is BG ; NewAcc = BG )), L, InitV, Out)], Goals)
        ; HV == 'map-atom', T = [List, XVar, Body]
          -> translate_expr_to_conj(List, ConjList, L),
             type_element_var(L, XVar),
             translate_expr_to_conj(Body, BodyCallConj, BodyCall),
             static_type(BodyCall, BT), set_static_type(Out, ['List', BT]),
             exclude(==(true), [ConjList], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [maplist([XVar, Y]>>(BodyCallConj, ( number(BodyCall) -> Y is BodyCall ; Y = BodyCall )), L, Out)], Goals)
        ; HV == 'filter-atom', T = [List, XVar, Cond]
          -> translate_expr_to_conj(List, ConjList, L),
             type_element_var(L, XVar),
             translate_expr_to_conj(Cond, CondConj, CondGoal),
             static_type(L, LT), set_static_type(Out, LT),
             exclude(==(true), [ConjList], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [include([XVar]>>(CondConj, CondGoal), L, Out)], Goals)
        ; HV == '|->', T = [Args, Body] -> next_lambda_name(F),
                                           % find free (non-argument) variables in Body
                                           term_variables(Body, AllVars),
                                           term_variables(Args, ArgVars),
                                           exclude({ArgVars}/[V]>>memberchk_eq(V, ArgVars), AllVars, FreeVars),
                                           append(FreeVars, Args, FullArgs),
                                           % compile clause with all bound + free vars, from a copy so that
                                           % what is learned inside the deferred body stays inside it
                                           copy_term([=, [F|FullArgs], Body], LambdaSource),
                                           translate_clause(LambdaSource, Clauses),
                                           register_fun(F),
                                           assert_translated(LambdaSource, Clauses, _),
                                           format(atom(Label), "metta lambda (~w)", [F]),
                                           maybe_print_compiled_clause(Label, ['|->', Args, Body], Clauses),
                                           length(FullArgs, N),
                                           Arity is N + 1,
                                           (arity(F, Arity) -> true ; assertz(arity(F, Arity))),
                                           % emit closure capturing the environment (free vars)
                                           ( FreeVars == [] -> Out = F
                                                             ; Out = partial(F, FreeVars) )
        %--- Spaces ---:
        %a row added to a space declared (SpaceOf Row) is checked against Row as
        %a boundary, and a pattern matched in it has the types of Row's parts:
        ; ( HV == 'add-atom' ; HV == 'remove-atom' ), T = [Space,Atom] ->
                                                                   translate_expr(Space, G1, S),
                                                                   ( HV == 'add-atom', atom(S), space_type(S, Row),
                                                                     \+ ( nonvar(Atom), Atom = [E|_], E == '=' )
                                                                     -> type_boundary(row(S), Atom, Row, Cs),
                                                                        append([GsH, G1, Cs, [add_sexp(S, Atom)]], Goals), Out = true
                                                                   ; Goal =.. [HV,S,Atom,Out],
                                                                     set_static_type(Out, 'Bool'),
                                                                     append([GsH,G1,[Goal]], Goals) )
        ; HV == match, T = [Space, Pattern, Body] -> translate_expr(Space, G1, S),
                                                     space_pattern(Space, Pattern, RuntimePattern, PatternGoals),
                                                     ( atom(S), space_type(S, Row) -> space_read_types(RuntimePattern, Row) ; true ),
                                                     translate_expr(Body, GsB, Out),
                                                     append([G1, [match(S, RuntimePattern, Out, Out)], PatternGoals, GsB], Goals)
        %--- Predicate to compiled goal ---:
        ; HV == translatePredicate, T = [Expr] -> Expr = [S|Args],
                                                  translate_args(Args, GsArgs, ArgsOut),
                                                  Goal =.. [S|ArgsOut],
                                                  append(GsH, GsArgs, Inner),
                                                  append(Inner, [Goal], Goals)
        %--- Manual dispatch options: ---
        %Generate a predicate call on compilation, translating Args for nesting:
        ; HV == call,  T = [Expr] -> Expr = [F|Args],
                                     route_args(F, Args, GsArgs, ArgsOut),
                                     type_call(F, ArgsOut, Out, Checks, Extra, Type),
                                     append([GsH, GsArgs, Checks], Inner),
                                     append(ArgsOut, [Out], CallArgs),
                                     Goal =.. [F|CallArgs],
                                     append(Inner, [Goal|Extra], Goals),
                                     set_static_type(Out, Type)
        %Produce a dynamic dispatch, translating Args for nesting:
        ; HV == reduce, T = [Expr] -> ( var(Expr) -> translate_expr(Expr, GsH, ExprOut),
                                                     Goals = [reduce(ExprOut, Out)|GsH]
                                                   ; Expr = [F|Args],
                                                     route_args(F, Args, GsArgs, ArgsOut),
                                                     ( atom(F), fun(F) -> type_call(F, ArgsOut, Out, Checks, Extra, Type)
                                                                        ; Checks = [], Extra = [], Type = '%Undefined%' ),
                                                     append([GsH, GsArgs, Checks], Inner),
                                                     ExprOut = [F|ArgsOut],
                                                     append(Inner, [reduce(ExprOut, Out)|Extra], Goals),
                                                     set_static_type(Out, Type) )
        %Invoke translator to evaluate MeTTa code as data/list:
        ; HV == eval, T = [Arg] -> ( nonvar(Arg), Arg = [Q, Quoted], Q == quote
                                     -> translate_expr(Quoted, GsQ, Out),           %(eval (quote E)) == E
                                        append(GsH, GsQ, Goals)
                                      ; append(GsH, [eval(Arg, Out)], Goals) )
        %Type ascription: E checked against T (statically where possible), and of type T from here on:
        ; HV == the, T = [TypeExpr, Expr] -> translate_expr(Expr, GsE, V),
                                             type_normalize(TypeExpr, Type),
                                             type_boundary(the(Type), V, Type, GsA),
                                             set_static_type(Out, Type),
                                             append([GsH, GsE, GsA, [Out = V]], Goals)
        %(brand N E): E checked against the representation of the Newtype N, and of type N from here on:
        ; HV == brand, T = [Name, Expr] -> translate_expr(Expr, GsE, V),
                                           newtype_representation(Name, Rep),
                                           type_boundary(brand(Name), V, Rep, GsA),
                                           set_static_type(Out, Name),
                                           append([GsH, GsE, GsA, [Out = V]], Goals)
        %Force arg to remain data/list:
        ; HV == quote, T = [Expr] -> Out = Expr,
                                     Goals = GsH
        ; HV == 'catch', T = [Expr] ->
          translate_expr(Expr, GsExpr, ExprOut),
          goals_list_to_conj(GsExpr, Conj),
          Goal = catch((Conj, Out = ExprOut),
                       Exception,
                       (Exception = error(Type, Ctx) -> Out = ['Error', Type, Ctx]
                                                      ; Out = ['Error', Exception, none])),
          append(GsH, [Goal], Goals)
        %--- Automatic 'smart' dispatch, translator deciding when to create a predicate call, data list, or dynamic dispatch: ---
        %Known function or closure => typed call:
        ; ( atom(HV), fun(HV) -> Fun = HV, Bound = []
          ; compound(HV), HV = partial(Fun, Bound) )
          -> translate_call(Fun, Bound, T, GsH, Goals, Out)
        %Literals (numbers, strings, etc.), known non-function atom => data:
        ; ( atomic(HV), \+ atom(HV) ; atom(HV), \+ fun(HV) )
          -> note_symbol_head(HV),
             translate_args(T, GsT, AVs),
             append(GsH, GsT, Goals),
             Out = [HV|AVs]
        %Plain data list: evaluate inner fun-sublists
        ; is_list(HV) -> translate_args(T, GsT, AVs),
                         append(GsH, GsT, Inner),
                         eval_data_term(HV, Gd, HV1),
                         append(Inner, Gd, Goals),
                         Out = [HV1|AVs]
        %Variable head applied to arguments: a closure call, checked against its
        %arrow type when that is known; a lone ($x) is dispatched at runtime.
        %The callee's own declaration decides whether an argument is evaluated
        %(see call_args/4):
        ; route_args(HV, T, GsT, AVs),
          append(GsH, GsT, Inner),
          ( var(HV), AVs \== []
            -> type_closure_call(HV, AVs, Out, Checks, Extra, Type),
               closure_apply_goal(HV, AVs, Out, Goal),
               append([Inner, Checks, [Goal], Extra], Goals),
               set_static_type(Out, Type)
          ; append(Inner, [reduce([HV|AVs], Out)], Goals) ) ).

%The arguments of a call whose callee is known only at runtime (through a
%variable, reduce, call, a generator): a known function's own policy holds or
%evaluates each, as at a direct call; with a variable head see call_args/4:
route_args(F, Args, Gs, AVs) :-
        ( atom(F), length(Args, N), type_arg_policy(F, N, Ps) -> translate_args_by_type(Args, Ps, Gs, AVs)
        ; var(F), Args \== [] -> call_args(F, Args, Gs, AVs)
        ; translate_args(Args, Gs, AVs) ).
%The arguments of a call through a variable: the callee, known only at runtime,
%decides as a direct call does. Its mask (held_mask/3) is read first, then an
%argument that computes is passed as its source where the callee holds it, and
%evaluated elsewhere; a position the head's known arrow type gives a value type
%is evaluated (the callee cannot hold it there):
call_args(HV, Args, Gs, AVs) :- static_type(HV, K), ( nonvar(K), K = [A|Ts0], A == '->' -> Ts = Ts0 ; Ts = [] ),
                                same_length(Args, Ps), call_args_(Args, Ts, Ps, ArgGs, AVs, false, Held),
                                ( Held == true -> length(Args, N), Gs = [( held_mask(HV, N, Ps) -> true ; true )|ArgGs]
                                ; Gs = ArgGs ).
call_args_([], _, [], [], [], H, H).
call_args_([A|As], Ts0, [P|Ps], Gs, [V|Vs], H0, H) :-
        ( Ts0 = [T|Ts] -> true ; T = '%Undefined%', Ts = [] ),
        ( computes(A), \+ value_position(T)
          -> expression_arg_value(A, Src), translate_expr_to_conj(A, Conj, VA),
             ( Conj == true -> Eval = (V = VA) ; Eval = (Conj, V = VA) ),
             G1 = [( P == 'Atom' -> V = Src ; Eval )], H1 = true
        ; translate_expr(A, G1, V), H1 = H0 ),
        call_args_(As, Ts, Ps, G2, Vs, H1, H), append(G1, G2, Gs).
computes([H|_]) :- atom(H), ( fun(H) ; syntax_head(H) ), !.
computes(L) :- is_list(L), member(X, L), is_list(X), computes(X), !.
value_position(T) :- nonvar(T), \+ wildcard_type(T), \+ T == 'Atom'.
wildcard_type(T) :- atom(T), memberchk(T, ['%Undefined%', 'Expression', '_']).
%The positions F, or a partial application of it, holds when called with N
%arguments: Atom there, unbound elsewhere; it fails for a callee that holds none:
held_mask(F, N, Ps) :- ( atom(F) -> may_hold(F), type_arg_policy(F, N, Ps)
                       ; compound(F), F = partial(G, Bs), atom(G), may_hold(G), length(Bs, K), M is K + N,
                         type_arg_policy(G, M, Ps0), length(Pre, K), append(Pre, Ps, Ps0) ).
%The heads this translator handles as syntax rather than as calls, those of
%translate_expr/3 and rewrite_streamops/2 (tests/test_syntax_heads.pl keeps the
%table complete), and those that translator rules add:
syntax_heads([data, 'make-list', superpose, collapse, cut, test, once, hyperpose, with_mutex, transaction,
              progn, prog1, if, case, 'and-then', 'or-else', let, chain, 'let*', sealed, forall, foldall,
              'foldl-atom', 'map-atom', 'filter-atom', '|->', 'add-atom', 'remove-atom', match,
              translatePredicate, call, reduce, eval, the, brand, quote, catch, 'trace!', unique,
              'alpha-unique', 'import!', union, intersection, subtraction]).
syntax_head(H) :- syntax_heads(Hs), memberchk(H, Hs), !.
syntax_head(H) :- translator_rule(H).

%An operand of and-then or or-else is checked as a Bool where it is evaluated
%(an operand that is skipped is never evaluated, so never checked):
translate_bool_operand(E, Conj, V) :- translate_expr(E, Gs, V), type_boundary(boolean, V, 'Bool', Cs),
                                     append(Gs, Cs, All), goals_list_to_conj(All, Conj).

%A let pattern is matched, not evaluated, where its head is a variable: such a
%sub-pattern is destructured as data (a function-headed one keeps PeTTa's
%evaluation, as (let (cons $h $t) ...) does):
translate_pattern(P, Gs, V) :- is_list(P), P = [H|_], var(H), !, translate_patterns(P, Gs, V).
translate_pattern(P, Gs, V) :- translate_expr(P, Gs, V).
translate_patterns([], [], []).
translate_patterns([P|Ps], Gs, [V|Vs]) :- translate_pattern(P, G1, V), translate_patterns(Ps, G2, Vs),
                                          append(G1, G2, Gs).

%In a space declared (SpaceOf Row), a pattern position applying a function
%with one det declaration constrains the matched value, as a clause head's
%functional pattern does; other functions there are payload tags, and in other
%spaces (&self holds source atoms such as (= (f $x) ...)) patterns are data:
space_pattern(Space, P, RP, Goals) :- atom(Space), space_type(Space, _), !, constrain_space_args(P, RP, Goals).
space_pattern(_, P, P, []).
constrain_space_args(X, X, []) :- ( var(X) ; atomic(X) ), !.
constrain_space_args([F, A, B], [A1|B1], Goals) :- F == cons, !, constrain_space_args(A, A1, G1), constrain_space_args(B, B1, G2),
                                                   append(G1, G2, Goals).
constrain_space_args([F|Args], V, Goals) :- atom(F), fun(F), is_list(Args), length(Args, N),
                                            findall(D, type_decl(F, N, _, _, D), [det]), !,
                                            translate_expr([F|Args], Gs, V), flatten(Gs, Goals).
constrain_space_args(In, Out, Goals) :- maplist(constrain_space_args, In, Out, Gss), flatten(Gss, Goals).

closure_apply_goal(HV, [A], Out, apply_fn1(HV, A, Out)) :- !.
closure_apply_goal(HV, [A, B], Out, apply_fn2(HV, A, B, Out)) :- !.
closure_apply_goal(HV, [A, B, C], Out, apply_fn3(HV, A, B, C, Out)) :- !.
closure_apply_goal(HV, AVs, Out, apply_fnN(HV, AVs, Out)).

%Runtime closure application: a function, or a partial application of one,
%that has the arity is called as a known call is, under its contract (see
%dynamic_call/4) and through its memo table; any other value is reduce/2's
%(data, or a partial application). Errors raised inside the callee propagate:
apply_fn1(F, A, Out) :- apply_fnN(F, [A], Out).
apply_fn2(F, A, B, Out) :- apply_fnN(F, [A, B], Out).
apply_fn3(F, A, B, C, Out) :- apply_fnN(F, [A, B, C], Out).
apply_fnN(F, Args, Out) :- ( atom(F) -> G = F, All = Args ; compound(F), F = partial(G, Bs), atom(G), append(Bs, Args, All) ),
                           length(All, N), Arity is N + 1, arity(G, Arity), current_predicate(G/Arity), !,
                           resolve_memoization(G, All, Out, Goal), dynamic_call(G, All, Out, Goal).
apply_fnN(F, Args, Out) :- reduce([F|Args], Out).

%A call of a known function: arguments are evaluated or held by the declared
%policy and checked against the declarations (see types.pl), then the function
%is called, inlined, specialized or partially applied:
translate_call(Fun, Bound, Args, GsH, Goals, Out) :-
        length(Args, NA), length(Bound, NB), N is NA + NB,
        ( type_arg_policy(Fun, N, Ps) -> length(BoundPs, NB), append(BoundPs, ArgPs, Ps) ; true ),
        translate_args_by_type(Args, ArgPs, GsT, AVs0),
        append(Bound, AVs0, AVs),
        type_call(Fun, AVs, Out, Checks, Extra, Type),
        append([GsH, GsT, Checks], Inner),
        ( Extra == [], arith_inline(Fun, AVs, Out, ArithGs)
          -> append(Inner, ArithGs, Goals)
           ; build_call_or_partial(Fun, AVs, Out, Inner, Extra, Goals) ),
        set_static_type(Out, Type).

%Builtin arithmetic compiles to native is/2, constant-folded when both
%operands are literals, while the builtin definition is untouched:
arith_inline(Fun, [A, B], Out, Gs) :- arith_op(Fun, A, B, Expr),
                                      builtin_untouched(Fun),
                                      ( number(A), number(B)
                                        -> catch((Out is Expr, Gs = []), _, Gs = [Out is Expr])
                                         ; Gs = [Out is Expr] ).

arith_op('+', A, B, A + B).
arith_op('-', A, B, A - B).
arith_op('*', A, B, A * B).
arith_op('/', A, B, A / B).
arith_op('%', A, B, A mod B).
arith_op(min, A, B, min(A, B)).
arith_op(max, A, B, max(A, B)).

builtin_untouched(F) :- functor(H, F, 3), predicate_property(H, number_of_clauses(1)).

%A builtin comparison whose result only feeds an if-condition compiles to the
%native comparison, skipping the true/false round-trip:
translate_if_cond(Cond, PreConj, CondGoal) :- translate_expr(Cond, GsC, Cv),
                                              ( var(Cv), append(Pre, [Last], GsC), reified_cond(Last, Cv, Native)
                                                -> goals_list_to_conj(Pre, PreConj), CondGoal = Native
                                                 ; goals_list_to_conj(GsC, PreConj), CondGoal = (Cv == true) ).

reified_cond(G, Cv, Native) :- nonvar(G), G =.. [F, A, B, R], R == Cv,
                               cmp_native(F, A, B, Native),
                               builtin_untouched(F).

cmp_native('<', A, B, (A < B)).
cmp_native('<=', A, B, (A =< B)).
cmp_native('>', A, B, (A > B)).
cmp_native('>=', A, B, (A >= B)).
cmp_native('==', A, B, (A == B)).
cmp_native('!=', A, B, (A \== B)).

%Generate actual function call or partial if arity not complete:
build_call_or_partial(Fun, AVs, Out, Inner, Extra, Goals) :- ( maybe_specialize_call(Fun, AVs, Out, Goal)
                                                               -> append(Inner, [Goal|Extra], Goals)
                                                                ; build_direct_call(Fun, AVs, Out, Inner, Extra, Goals) ).

build_direct_call(Fun, AVs, Out, Inner, Extra, Goals) :- length(AVs, N),
                                                         Arity is N + 1,
                                                         ( ( current_predicate(Fun/Arity) ; catch(arity(Fun, Arity), _, fail) ),
                                                           \+ ( current_op(_, _, Fun), Arity =< 2 )
                                                           -> resolve_memoization(Fun, AVs, Out, Goal),
                                                              append(Inner, [Goal|Extra], Goals)
                                                         ; incomplete_application_kind(Fun, Arity, partial)
                                                           -> Out = partial(Fun, AVs),
                                                              append(Inner, Extra, Goals)
                                                            ; append(Inner, [throw_function_overapplication(Fun, N)|Extra], Goals) ).

%Selectively translate non-Atom args while Atom args stay as data input:
translate_args_by_type([], _, [], []) :- !.
translate_args_by_type([A|As], [T|Ts], GsOut, [AV|AVs]) :-
                      ( T == 'Atom' -> expression_arg_value(A, AV), GsA = []
                                     ; translate_expr(A, GsA, AV) ),
                      translate_args_by_type(As, Ts, GsRest, AVs),
                      append(GsA, GsRest, GsOut).

%Atom-typed args stay unevaluated data, except underapplied callable
%expressions representable as a goal-free closure:
expression_arg_value(A, AV) :- nonvar(A), A = [B, _, Inner], B == brand, !,      %a brand is erased, held or not
                               expression_arg_value(Inner, AV).
expression_arg_value(A, AV) :- ( maybe_closure_expr(A),
                                 catch(( translate_expr(A, GsExpr, AVExpr),
                                         trivial_goals(GsExpr),
                                         callable_expression_value(AVExpr) ),
                                       error(_, typecheck), fail)
                                 -> AV = AVExpr
                                  ; AV = A ).

%An underapplied call to a known function (would compile to partial(...)):
maybe_closure_expr([F|Args]) :- atom(F), fun(F), is_list(Args),
                                length(Args, N), Arity is N + 1,
                                \+ ( ( current_predicate(F/Arity) ; catch(arity(F, Arity), _, fail) ),
                                     \+ ( current_op(_, _, F), Arity =< 2 ) ).

trivial_goals([]).
trivial_goals([true|Gs]) :- trivial_goals(Gs).

callable_expression_value(AV) :- atom(AV), fun(AV).
callable_expression_value(partial(Fun, Bound)) :- atom(Fun), ground(Bound).

%Handle data list:
eval_data_term(X, [], X) :- (var(X); atomic(X)), !.
eval_data_term([F|As], Goals, Val) :- ( atom(F), fun(F) -> translate_expr([F|As], Goals, Val)
                                                         ; eval_data_list([F|As], Goals, Val) ).

%Handle data list entry:
eval_data_list([], [], []).
eval_data_list([E|Es], Goals, [V|Vs]) :- ( is_list(E) -> eval_data_term(E, G1, V) ; V = E, G1 = [] ),
                                         eval_data_list(Es, G2, Vs),
                                         append(G1, G2, Goals).

%Convert let* to recusrive let:
letstar_to_rec_let([[Pat,Val]],Body,[let,Pat,Val,Body]).
letstar_to_rec_let([[Pat,Val]|Rest],Body,[let,Pat,Val,Out]) :- letstar_to_rec_let(Rest,Body,Out).

%Patterns: variables, atoms, numbers, lists:
translate_pattern(X, X) :- var(X), !.
translate_pattern(X, X) :- atomic(X), !.
translate_pattern([H|T], [P|Ps]) :- !, translate_pattern(H, P),
                                       translate_pattern(T, Ps).

% Constructs the goal for a single branch of an if-then-else/case.
build_branch(true, Val, Out, (Out = Val)) :- !.
build_branch(Con, Val, Out, Goal) :- var(Val) -> Val = Out, Goal = Con
                                               ; Goal = (Val = Out, Con).

%The key of a case with an Empty case runs once, and Empty only if the key yields no value. Soft-cut does exactly
%this, but would make a cut inside the key local to it; so a key containing a cut instead records in a fresh
%non-backtrackable flag whether it yielded a value, and its cut still commits the clause:
case_with_empty(GkConj, CaseGoal, DefaultThen, ( GkConj *-> CaseGoal ; DefaultThen )) :- \+ ( sub_term(G, GkConj), G == ! ), !.
case_with_empty(GkConj, CaseGoal, DefaultThen, ( functor(Seen, seen, 1),
                                                 ( GkConj, nb_setarg(1, Seen, true), CaseGoal
                                                 ; arg(1, Seen, S), var(S), DefaultThen ) )).

%Translate case expression recursively into nested if, collecting the branch value types:
translate_case([[K,VExpr]|Rs], Kv, Out, Goal, KGo, [VT|VTs]) :- constrain_args(K, Kc, Gc),
                                                                static_type(Kv, KT), type_pattern(Kc, KT),
                                                                translate_expr_to_conj(VExpr, ConV, VOut),
                                                                static_type(VOut, VT),
                                                                build_branch(ConV, VOut, Out, Then),
                                                                ( Rs == [] -> Goal = ((Kv = Kc) -> Then), KGi=[], VTs = []
                                                                            ; translate_case(Rs, Kv, Out, Next, KGi, VTs),
                                                                              Goal = ((Kv = Kc) -> Then ; Next) ),
                                                                append([Gc,KGi], KGo).

%Translate arguments recursively:
translate_args([], [], []).
translate_args([X|Xs], Goals, [V|Vs]) :- translate_expr(X, G1, V),
                                         translate_args(Xs, G2, Vs),
                                         append(G1, G2, Goals).

%Build A ; B ; C ... from a list:
disj_list([G], G).
disj_list([G|Gs], (G ; R)) :- disj_list(Gs, R).

%Build one disjunct per branch: (Conj, Out = Val), with the branch value types:
build_superpose_branches([], _, [], []).
build_superpose_branches([E|Es], Out, [B|Bs], [T|Ts]) :- translate_expr_to_conj(E, Conj, Val),
                                                         static_type(Val, T),
                                                         build_branch(Conj, Val, Out, B),
                                                         build_superpose_branches(Es, Out, Bs, Ts).

%Build hyperpose branch as a goal list for concurrent_maplist to consume:
build_hyperpose_branches([], [], []).
build_hyperpose_branches([E|Es], [(Goal, Res)|Bs], [T|Ts]) :- translate_expr_to_conj(E, Goal, Res),
                                                              static_type(Res, T),
                                                              build_hyperpose_branches(Es, Bs, Ts).

%Runtime hyperpose path for variable/computed list arguments.
hyperpose_runtime(Exprs, Out) :- is_list(Exprs),
                                 concurrent_and(member(Expr, Exprs), eval(Expr, Out)).

%Like membercheck but with direct equality rather than unification
memberchk_eq(V, [H|_]) :- V == H, !.
memberchk_eq(V, [_|T]) :- memberchk_eq(V, T).

%Generate readable lambda name:
next_lambda_name(Name) :- ( nb_current(lambda_counter, Prev) -> true ; Prev = 0 ),
                          N is Prev + 1,
                          nb_setval(lambda_counter, N),
                          format(atom(Name), 'lambda_~d', [N]).
