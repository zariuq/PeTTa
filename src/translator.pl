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

%Flatten (= Head Body) MeTTa function into Prolog Clause. A function with one
%declaration has its parameters typed by it and its result checked against it
%(see types.pl); -[det]-> and -[semidet]-> functions commit to the first clause
%whose head matches:
translate_clause(Input, Clause) :- translate_clause(Input, Clause, true).
translate_clause(Input, (Head :- BodyConj), ConstrainArgs) :-
                                               Input = [=, [F|Args0], BodyExpr],
                                               length(Args0, N),
                                               ( ConstrainArgs -> maplist(constrain_args, Args0, Args1, GoalsA),
                                                                  flatten(GoalsA,GoalsPrefix)
                                                                ; Args1 = Args0, GoalsPrefix = [] ),
                                               ( atom(F), nb_current(F, Prev) -> true ; Prev = [] ),
                                               copy_term_nat(fun_meta(Args1, BodyExpr), Meta),
                                               nb_setval(F, [Meta | Prev]),
                                               %parameters get the declared types, as instantiated by constant
                                               %head arguments (a specialization's closure); the type variables
                                               %left are the caller's choice, unknown here:
                                               ( unique_type_decl(F, N, ATs, OT, Det) -> type_instantiate(Args1, ATs),
                                                                                       opaque_type(ATs, PTs),
                                                                                       maplist(type_pattern, Args1, PTs)
                                                                                     ; OT = '%Undefined%', Det = plain ),
                                               with_compiling(F, translate_declared_body(F, N, BodyExpr, GoalsBody, ExpOut)),
                                               (  nonvar(ExpOut) , ExpOut = partial(Base,Bound)
                                               -> arity(Base, Arity), length(Bound, NB), M is (Arity - NB) - 1,
                                                  length(ExtraArgs, M), append(Bound, ExtraArgs, CallInArgs),
                                                  resolve_memoization(Base, CallInArgs, Out, Goal),
                                                  append(GoalsBody,[Goal],FinalGoals), append(Args1,ExtraArgs,HeadArgs),
                                                  OutChecks = []
                                               ; FinalGoals= GoalsBody , HeadArgs = Args1, Out = ExpOut,
                                                 ( ground(OT) -> type_boundary(output(F), Out, OT, OutChecks) ; OutChecks = [] ) ),
                                               append(HeadArgs, [Out], FinalArgs),
                                               Head =.. [F|FinalArgs],
                                               length(FinalArgs, CompiledArity),
                                               (arity(F, CompiledArity) -> true ; assertz(arity(F, CompiledArity))),
                                               ( memberchk(Det, [det, semidet]) -> Commit = [!] ; Commit = [] ),
                                               append([GoalsPrefix, Commit, FinalGoals, OutChecks], Goals),
                                               goals_list_to_conj(Goals, BodyConj).

%A function declared to return Atom returns its body as data:
translate_declared_body(F, N, Expr, [], Expr) :- atom(F), type_decl(F, N, _, Out, _), Out == 'Atom', !.
translate_declared_body(_, _, Expr, Goals, Out) :- translate_expr(Expr, Goals, Out).

with_compiling(F, Goal) :- ( nb_current('$compiling', Prev) -> true ; Prev = none ),
                           setup_call_cleanup(b_setval('$compiling', F), Goal, b_setval('$compiling', Prev)).

%Retranslate F's clauses in source order, once they all translate: a type
%declaration arrived late, or a name they used as data became a function.
recompile_function_clauses(F) :- findall(Ref-Term, ( translated_from(Ref, Term), Term = [=, [G|_], _], G == F,
                                                     clause(_, _, Ref) ), Us),
                                 ( Us == [] -> true
                                 ; ( nb_current(F, Metas) -> true ; Metas = [] ),
                                   nb_setval(F, []),
                                   ( catch(maplist([_-Term, Term-Clause]>>translate_clause(Term, Clause), Us, TCs), E, true) -> true ; true ),
                                   ( nonvar(TCs), var(E)
                                     -> forall(member(Ref-_, Us), ( retractall(translated_from(Ref, _)), erase(Ref) )),
                                        forall(member(Term-Clause, TCs), ( assertz(Clause, Ref), assertz(translated_from(Ref, Term)) )),
                                        invalidate_specializations(F)
                                      ; nb_setval(F, Metas),
                                        ( nonvar(E) -> throw(E) ; true ) ) ).

%Record atoms compiled as plain symbol heads, so a late function registration
%can be flagged, and the clauses that used it as data retranslated:
:- dynamic symbol_head/1.
note_symbol_head(HV) :- atom(HV), !,
                        ( symbol_head(HV) -> true ; assertz(symbol_head(HV)) ),
                        ( nb_current('$compiling', F), F \== none, \+ symbol_use(HV, F) -> assertz(symbol_use(HV, F)) ; true ).
note_symbol_head(_).
late_function(F) :- forall(retract(symbol_use(F, G)), ( G == F -> true ; recompile_function_clauses(G) )).

%Print compiled clause:
maybe_print_compiled_clause(_, _, _) :- silent(true), !.
maybe_print_compiled_clause(Label, FormTerm, Clause) :-
    swrite(FormTerm, FormStr),
    format("\e[33m-->  ~w  -->~n\e[36m~w~n\e[33m--> prolog clause -->~n\e[32m", [Label, FormStr]),
    portray_clause(current_output, Clause),
    format("\e[33m^^^^^^^^^^^^^^^^^^^^^~n\e[0m").

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
                                 catch(call(Goal), _, fail)
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
                                                        join_static_types(Types, Type), force_static_type(Out, Type),
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
        ; HV == once, T = [X] -> translate_expr_to_conj(X, Conj, Out),
                                 append(GsH, [once(Conj)], Goals)
        ; HV == hyperpose, T = [L]
          -> ( nonvar(L), is_list(L)
               -> build_hyperpose_branches(L, Branches),
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
                                        force_static_type(Out, TT),
                                        ( ConC == true -> append(GsH, [ ( CondGoal -> BT ) ], Goals)
                                                        ; append(GsH, [ ( ConC, ( CondGoal -> BT ) ) ], Goals) )
        ; HV == if, T = [Cond, Then, Else] -> translate_if_cond(Cond, ConC, CondGoal),
                                              translate_expr_to_conj(Then, ConT, Tv),
                                              translate_expr_to_conj(Else, ConE, Ev),
                                              static_type(Tv, TT), static_type(Ev, TE),
                                              build_branch(ConT, Tv, Out, BT),
                                              build_branch(ConE, Ev, Out, BE),
                                              join_static_types([TT, TE], Type), force_static_type(Out, Type),
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
                                                       join_static_types([DT|Types], Type), force_static_type(Out, Type),
                                                       case_with_empty(GkConj, CaseGoal, DefaultThen, Combined),
                                                       append([GsH, KeyGoal, [Combined]], Goals)
                                                     ; translate_expr(KeyExpr, Gk, Kv),
                                                       translate_case(PairsExpr, Kv, Out, IfGoal, KeyGoal, Types),
                                                       join_static_types(Types, Type), force_static_type(Out, Type),
                                                       append([GsH, Gk, KeyGoal, [IfGoal]], Goals) )
        %--- Short-circuit boolean operators ---:
        ; HV == 'and-then', T = [A, B] -> translate_expr_to_conj(A, ConjA, Av),
                                           translate_expr_to_conj(B, ConjB, Bv),
                                           type_boundary(native, Av, 'Bool', _), type_boundary(native, Bv, 'Bool', _),
                                           set_static_type(Out, 'Bool'),
                                           append(GsH, [(ConjA, (Av == true -> (ConjB, Out = Bv) ; Out = false))], Goals)
        ; HV == 'or-else', T = [A, B] -> translate_expr_to_conj(A, ConjA, Av),
                                          translate_expr_to_conj(B, ConjB, Bv),
                                          type_boundary(native, Av, 'Bool', _), type_boundary(native, Bv, 'Bool', _),
                                          set_static_type(Out, 'Bool'),
                                          append(GsH, [(ConjA, (Av == true -> Out = true ; (ConjB, Out = Bv)))], Goals)
        %--- Unification constructs ---:
        ; (HV == let ; HV == chain), T = [Pat, Val, In] -> translate_expr(Pat, Gp, Pv),
                                                           translate_expr(Val, Gv, V),
                                                           static_type(V, VT), type_pattern(Pv, VT),
                                                           translate_expr(In,  Gi, Out),
                                                           append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
        ; HV == 'let*', T = [Binds, Body] -> letstar_to_rec_let(Binds,Body,RecLet),
                                             translate_expr(RecLet,  Goals, Out)
        ; HV == sealed, T = [Vars, Expr] -> translate_expr_to_conj(Expr, Con, Val),
                                            Goals = [copy_term(Vars,[Con,Val],_,[Ncon,Out]),Ncon]
        %--- Iterating over non-deterministic generators without reification ---:
        ; HV == 'forall', T = [GF, TF]
          -> ( is_list(GF) -> GF = [GFH|GFA],
                              translate_expr(GFH, GsGFH, GFHV),
                              translate_args(GFA, GsGFA, GFAv),
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
                              translate_args(GFA, GsGFA, GFAv),
                              append(GsGFH, GsGFA, GsGF),
                              GenList = [GFHV|GFAv]
                            ; translate_expr(GF, GsGF, GFHV),
                              GenList = [GFHV] ),
             append(GsH, GsAF, Tmp1),
             append(Tmp1, GsGF, Tmp2),
             append(Tmp2, [ConjInit, foldall(agg_reduce(AFV, V), reduce(GenList, V), Init, Out)], Goals)
        %--- Higher-order functions with pseudo-lambdas and lambdas ---:
        ; HV == 'foldl-atom', T = [List, Init, AccVar, XVar, Body]
          -> translate_expr_to_conj(List, ConjList, L),
             translate_expr_to_conj(Init, ConjInit, InitV),
             translate_expr_to_conj(Body, BodyConj, BG),
             exclude(==(true), [ConjList, ConjInit], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [foldl([XVar, AccVar, NewAcc]>>(BodyConj, ( number(BG) -> NewAcc is BG ; NewAcc = BG )), L, InitV, Out)], Goals)
        ; HV == 'map-atom', T = [List, XVar, Body]
          -> translate_expr_to_conj(List, ConjList, L),
             translate_expr_to_conj(Body, BodyCallConj, BodyCall),
             exclude(==(true), [ConjList], CleanConjs),
             append(GsH, CleanConjs, GsMid),
             append(GsMid, [maplist([XVar, Y]>>(BodyCallConj, ( number(BodyCall) -> Y is BodyCall ; Y = BodyCall )), L, Out)], Goals)
        ; HV == 'filter-atom', T = [List, XVar, Cond]
          -> translate_expr_to_conj(List, ConjList, L),
             translate_expr_to_conj(Cond, CondConj, CondGoal),
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
                                           translate_clause(LambdaSource, Clause),
                                           register_fun(F),
                                           assertz(Clause, Ref),
                                           assertz(translated_from(Ref, LambdaSource)),
                                           format(atom(Label), "metta lambda (~w)", [F]),
                                           maybe_print_compiled_clause(Label, ['|->', Args, Body], Clause),
                                           length(FullArgs, N),
                                           Arity is N + 1,
                                           (arity(F, Arity) -> true ; assertz(arity(F, Arity))),
                                           % emit closure capturing the environment (free vars)
                                           ( FreeVars == [] -> Out = F
                                                             ; Out = partial(F, FreeVars) )
        %--- Spaces ---:
        ; ( HV == 'add-atom' ; HV == 'remove-atom' ), T = [Space,Atom] ->
                                                                   translate_expr(Space, G1, S),
                                                                   Goal =.. [HV,S,Atom,Out],
                                                                   set_static_type(Out, 'Bool'),
                                                                   append([GsH,G1,[Goal]], Goals)
        ; HV == match, T = [Space, Pattern, Body] -> translate_expr(Space, G1, S),
                                                     translate_expr(Body, GsB, Out),
                                                     append(G1, [match(S, Pattern, Out, Out)], G2),
                                                     append(G2, GsB, Goals)
        %--- Predicate to compiled goal ---:
        ; HV == translatePredicate, T = [Expr] -> Expr = [S|Args],
                                                  translate_args(Args, GsArgs, ArgsOut),
                                                  Goal =.. [S|ArgsOut],
                                                  append(GsH, GsArgs, Inner),
                                                  append(Inner, [Goal], Goals)
        %--- Manual dispatch options: ---
        %Generate a predicate call on compilation, translating Args for nesting:
        ; HV == call,  T = [Expr] -> Expr = [F|Args],
                                     translate_args(Args, GsArgs, ArgsOut),
                                     append(GsH, GsArgs, Inner),
                                     append(ArgsOut, [Out], CallArgs),
                                     Goal =.. [F|CallArgs],
                                     append(Inner, [Goal], Goals)
        %Produce a dynamic dispatch, translating Args for nesting:
        ; HV == reduce, T = [Expr] -> ( var(Expr) -> translate_expr(Expr, GsH, ExprOut),
                                                     Goals = [reduce(ExprOut, Out)|GsH]
                                                   ; Expr = [F|Args],
                                                     translate_args(Args, GsArgs, ArgsOut),
                                                     append(GsH, GsArgs, Inner),
                                                     ExprOut = [F|ArgsOut],
                                                     append(Inner, [reduce(ExprOut, Out)], Goals) )
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
        %arrow type when that is known; a lone ($x) is dispatched at runtime:
        ; translate_args(T, GsT, AVs),
          append(GsH, GsT, Inner),
          ( var(HV), AVs \== []
            -> ( static_type(HV, K), nonvar(K), K = [A|_], A == '->', copy_term(K, [_|Ts]),
                 length(AVs, NA), length(Ts, NT), NT > NA
                 -> length(ATs, NA), append(ATs, Rest, Ts),
                    type_boundary_args(closure, AVs, ATs, Checks),
                    ( Rest = [RT] -> result_static_type(ATs, RT, OutT)
                                   ; result_static_type(ATs, ['->'|Rest], OutT) ),
                    set_static_type(Out, OutT)
                  ; Checks = [] ),
               closure_apply_goal(HV, AVs, Out, Goal),
               append([Inner, Checks, [Goal]], Goals)
          ; append(Inner, [reduce([HV|AVs], Out)], Goals) ) ).

closure_apply_goal(HV, [A], Out, apply_fn1(HV, A, Out)) :- !.
closure_apply_goal(HV, [A, B], Out, apply_fn2(HV, A, B, Out)) :- !.
closure_apply_goal(HV, [A, B, C], Out, apply_fn3(HV, A, B, C, Out)) :- !.
closure_apply_goal(HV, AVs, Out, apply_fnN(HV, AVs, Out)).

%Runtime closure application; the last clause keeps reduce/2 semantics for
%values that are not callable at this arity (data, or a partial application).
%Errors raised inside the callee propagate:
apply_fn1(F, A, Out) :- atom(F), arity(F, 2), !, safe_apply(call(F, A, Out)).
apply_fn1(P, A, Out) :- compound(P), P = partial(F, Bs), length(Bs, K), Arity is K + 2, arity(F, Arity), !,
                        append(Bs, [A, Out], CallArgs),
                        Goal =.. [F|CallArgs], safe_apply(Goal).
apply_fn1(F, A, Out) :- reduce([F, A], Out).

apply_fn2(F, A, B, Out) :- atom(F), arity(F, 3), !, safe_apply(call(F, A, B, Out)).
apply_fn2(P, A, B, Out) :- compound(P), P = partial(F, Bs), length(Bs, K), Arity is K + 3, arity(F, Arity), !,
                           append(Bs, [A, B, Out], CallArgs),
                           Goal =.. [F|CallArgs], safe_apply(Goal).
apply_fn2(F, A, B, Out) :- reduce([F, A, B], Out).

apply_fn3(F, A, B, C, Out) :- atom(F), arity(F, 4), !, safe_apply(call(F, A, B, C, Out)).
apply_fn3(P, A, B, C, Out) :- compound(P), P = partial(F, Bs), length(Bs, K), Arity is K + 4, arity(F, Arity), !,
                              append(Bs, [A, B, C, Out], CallArgs),
                              Goal =.. [F|CallArgs], safe_apply(Goal).
apply_fn3(F, A, B, C, Out) :- reduce([F, A, B, C], Out).

apply_fnN(F, Args, Out) :- atom(F), length(Args, N), Arity is N + 1, arity(F, Arity), !,
                           append(Args, [Out], CallArgs), Goal =.. [F|CallArgs], safe_apply(Goal).
apply_fnN(P, Args, Out) :- compound(P), P = partial(F, Bs), append(Bs, Args, All),
                           length(All, N), Arity is N + 1, arity(F, Arity), !, append(All, [Out], CallArgs),
                           Goal =.. [F|CallArgs], safe_apply(Goal).
apply_fnN(F, Args, Out) :- reduce([F|Args], Out).

safe_apply(Goal) :- catch(Goal, error(existence_error(procedure, _), _), fail).

%A call of a known function: arguments are evaluated or held by the declared
%policy and checked against the declarations (see types.pl), then the function
%is called, inlined, specialized or partially applied:
translate_call(Fun, Bound, Args, GsH, Goals, Out) :-
        length(Args, NA), length(Bound, NB), N is NA + NB,
        ( type_arg_policy(Fun, N, Ps) -> length(BoundPs, NB), append(BoundPs, ArgPs, Ps) ; true ),
        translate_args_by_type(Args, ArgPs, GsT, AVs0),
        append(Bound, AVs0, AVs),
        ( native_builtin(Fun) -> Ctx = native ; Ctx = Fun ),
        findall(d(As, O), type_decl(Fun, N, As, O, _), Ds),
        ( Ds = [d(As, O)] -> type_boundary_args(Ctx, AVs, As, Checks), Extra = [], result_static_type(As, O, Type)
        ; Ds = [_,_|_] -> type_overload(Ctx, Fun, AVs, Out, Ds, Checks, Extra, Type)
        %a partial application checks the arguments it is given:
        ; Arity is N + 1, \+ arity(Fun, Arity),
          findall(As, (type_decl(Fun, M, As0, _, _), M > N, length(As, N), append(As, _, As0)), [As])
          -> type_boundary_args(Ctx, AVs, As, Checks), Extra = [], Type = '%Undefined%'
        ; ( Fun == cons ; Fun == 'cons-atom' ), AVs = [H, Tl] -> Checks = [], Extra = [], cons_static_type(H, Tl, Type)
        ; Checks = [], Extra = [], Type = '%Undefined%' ),
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
build_hyperpose_branches([], []).
build_hyperpose_branches([E|Es], [(Goal, Res)|Bs]) :- translate_expr_to_conj(E, Goal, Res),
                                                      build_hyperpose_branches(Es, Bs).

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
