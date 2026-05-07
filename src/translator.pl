% Internal MeTTa -> Prolog runtime compiler used by PeTTa at load/eval time.
% This is not the canonical file-to-file PeTTa <-> HE translator; that lives
% in /home/zar/claude/hyperon/translators/.

%Pattern matching, structural and functional/relational constraints on arguments:
constrain_args(X, X, []) :- (var(X); atomic(X)), !.
constrain_args([F, A, B], Out, Goals) :- nonvar(F),
                                         F == cons,
                                         constrain_args(A, A1, G1),
                                         constrain_args(B, B1, G2),
                                         Out = [A1|B1],
                                         append(G1, G2, Goals), !.
constrain_args([F|Args], Var, Goals) :- he_profile_enabled,
                                        atom(F),
                                        he_constructor_symbol(F), !,
                                        maplist(constrain_args, Args, OutArgs, NestedGoalsList),
                                        flatten(NestedGoalsList, NestedGoals),
                                        append(NestedGoals, [he_unify_clause_pattern([F|OutArgs], Var)], Goals).
constrain_args([F|Args], Var, Goals) :- atom(F),
                                        fun(F), !,
                                        translate_expr([F|Args], GoalsExpr, Var),
                                        flatten(GoalsExpr, Goals).
constrain_args(In, Out, Goals) :- maplist(constrain_args, In, Out, NestedGoalsList),
                                  flatten(NestedGoalsList, Goals), !.

he_unify_clause_pattern(Expected, Actual) :-
    he_clause_pattern_equiv(Expected, Actual).

he_clause_pattern_equiv(Expected, Actual) :-
    var(Expected), !,
    Expected = Actual.
he_clause_pattern_equiv(Expected, Actual) :-
    atomic(Expected), !,
    Expected = Actual.
he_clause_pattern_equiv(Expected, Actual) :-
    nonvar(Expected),
    Expected = [Head, Packet],
    nonvar(Head),
    Head == 'superpose-bind',
    nonvar(Actual),
    is_list(Actual), !,
    Packet = Actual.
he_clause_pattern_equiv([Head|ExpectedArgs], Actual) :-
    atom(Head),
    he_call_is_partial_arity(Head, ExpectedArgs),
    nonvar(Actual),
    Actual = partial(Head, ActualArgs), !,
    same_length(ExpectedArgs, ActualArgs),
    maplist(he_clause_pattern_equiv, ExpectedArgs, ActualArgs).
he_clause_pattern_equiv([Head|ExpectedArgs], [Head|ActualArgs]) :-
    same_length(ExpectedArgs, ActualArgs),
    maplist(he_clause_pattern_equiv, ExpectedArgs, ActualArgs), !.
he_clause_pattern_equiv(Expected, Actual) :-
    Expected = Actual.

%Flatten (= Head Body) MeTTa function into Prolog Clause:
translate_clause(Input, Clause) :- translate_clause(Input, Clause, true).
translate_clause(Input, Clause, ConstrainArgs) :-
                                               Input = [=, [F|_], _],
                                               atom(F),
                                               translate_clause(Input, Clause, ConstrainArgs, F).
translate_clause(Input, (Head :- BodyConj), ConstrainArgs, HeadFunctor) :-
                                               Input = [=, [F|Args0], BodyExpr],
                                               atom(F),
                                               ( he_bridge_clause_constrains_args(ConstrainArgs)
                                               -> maplist(constrain_args, Args0, Args1, GoalsA),
                                                  flatten(GoalsA,GoalsPrefix)
                                               ;  Args1 = Args0,
                                                  GoalsPrefix = [] ),
                                               catch(nb_getval(F, Prev), _, Prev = []),
                                               nb_setval(F, [fun_meta(Args1, BodyExpr) | Prev]),
                                               ( he_bridge_lower_clause_body(BodyExpr, GoalsBody, ExpOut)
                                               -> true
                                               ;  translate_expr(BodyExpr, GoalsBody, ExpOut) ),
                                               (  nonvar(ExpOut) , ExpOut = partial(Base,Bound)
                                               -> current_predicate(Base/Arity), length(Bound, N), M is (Arity - N) - 1,
                                                  length(ExtraArgs, M), append([Bound,ExtraArgs,[Out]],CallArgs), Goal =.. [Base|CallArgs],
                                                  append(GoalsBody,[Goal],FinalGoals), append(Args1,ExtraArgs,HeadArgs)
                                               ; FinalGoals= GoalsBody , HeadArgs = Args1, Out = ExpOut ),
                                               append(HeadArgs, [Out], FinalArgs),
                                               Head =.. [HeadFunctor|FinalArgs],
                                               append(GoalsPrefix, FinalGoals, Goals),
                                               goals_list_to_conj(Goals, BodyConj).

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

call_clause_functor(F, Arity, F) :-
    he_profile_enabled,
    current_predicate(F/Arity),
    \+ (current_op(_, _, F), Arity =< 2), !.
call_clause_functor(F, _Arity, ClauseF) :-
    he_clause_functor(F, ClauseF).

% Runtime dispatcher: call F if it's a registered fun/1, else keep as list:
reduce([F|Args], Out) :- nonvar(F), atom(F), fun(F)
                         -> % --- Case 1: callable predicate ---
                            he_bridge_reduce(F, Args, Out)
                          ; % --- Case 2: partial closure ---
                            compound(F), F = partial(Base, Bound) -> append(Bound, Args, NewArgs),
                                                                     reduce([Base|NewArgs], Out)
                          ; % --- Case 3: leave unevaluated ---
                            Out = [F|Args],
                            \+ cyclic_term(Out).

%Calling reduce from aggregate function foldall needs this argument wrapping
agg_reduce(AF, Acc, Val, NewAcc) :- reduce([AF, Acc, Val], NewAcc).

%Combined expr translation to goals list
translate_expr_to_conj(Input, Conj, Out) :-
        he_profile_enabled,
        atom(Input),
        he_zero_arg_user_callable_atom(Input), !,
        Conj = he_eval_or_reduce([Input], Out).
translate_expr_to_conj(Input, Conj, Out) :- translate_expr(Input, Goals, Out),
                                            goals_list_to_conj(Goals, Conj).

%Special stream operation rewrite rules before main translation
rewrite_streamops(['trace!', Arg1, Arg2],
                  ['trace!', Arg1, Arg2]) :-
    he_profile_enabled, !.
rewrite_streamops(['trace!', Arg1, Arg2],
                  [progn, ['println!', Arg1], Arg2]).
rewrite_streamops([unique, Arg],
                  [call, [superpose, ['unique-atom', [collapse, Arg]]]]).
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
translate_expr(X, [], Value) :-
        he_profile_enabled,
        atom(X),
        he_ground_numeric_constant(X, Value), !.
translate_expr(X, [], X)          :- ((var(X) ; atomic(X)) ; X = partial(_,_)), !.
translate_expr([H0|T0], Goals, Out) :-
        safe_rewrite_streamops([H0|T0],[H|T]),
        ( he_profile_enabled,
          nonvar(H),
          H = ['superpose-bind', PayloadExpr],
          T \= []
        -> translate_expr(PayloadExpr, GsPayload, Payload),
           translate_args(T, GsArgs, AVs),
           append([GsPayload, GsArgs, [he_superpose_bind_apply(Payload, AVs, Out)]], Goals)
        ;
        translate_expr(H, GsH, HV0),
        he_namespace_sugar_alias(HV0, HV),
        %--- Translator rules ---:
        ( nonvar(HV), translator_rule(HV) -> ( catch(match('&self', [':', HV, TypeChain], TypeChain, TypeChain), _, fail)
                                               -> TypeChain = [->|Xs],
                                                  append(ArgTypes, [_], Xs),
                                                  translate_args_by_type(T, ArgTypes, GsT, T1)
                                                ; translate_args(T, GsT, T1) ),
                                             append(T1,[Gs],Args),
                                             he_clause_functor(HV, HookFunctor),
                                             HookCall =.. [HookFunctor|Args],
                                             call(HookCall),
                                             translate_expr(Gs, GsE, Out),
                                             append([GsH,GsT,GsE],Goals)
        %--- Non-determinism ---:
        ; HV == superpose, T = [Args], is_list(Args), he_profile_enabled
          -> he_superpose_effect_branches(Args, Branches),
             append(GsH, [he_run_superpose_branches(Branches, Out)], Goals)
        ; HV == superpose, T = [Args], is_list(Args) -> build_superpose_branches(Args, Out, Branches),
                                                        disj_list(Branches, Disj),
                                                        append(GsH, [Disj], Goals)
        ; HV == collapse,
          T = [[once, [match, SpaceExpr, Pattern, Body]]],
          he_profile_enabled,
          ( Body == true ; Body == 'True' )
          -> translate_expr(SpaceExpr, GsS, S),
             append([GsH, GsS, [he_match_once_truth_list(S, Pattern, Out)]], Goals)
        ; HV == collapse, T = [E], he_profile_enabled
          -> translate_expr_to_conj(E, Conj, EV),
             append(GsH, [he_collect_visible_results(Conj, EV, Out)], Goals)
        ; HV == collapse, T = [E] -> translate_expr_to_conj(E, Conj, EV),
                                     append(GsH, [findall(EV, Conj, Out)], Goals)
        ; he_pre_builtin_dispatch(HV, T, GsH, Out, Goals)
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
		; HV == once, T = [[hyperpose, L]],
		  nonvar(L), is_list(L)
		  -> build_hyperpose_once_branches(L, Out, Branches),
		     append(GsH, [first_solution(Out, Branches, [on_fail(continue)])], Goals)
		; HV == once, T = [X], he_profile_enabled
		  -> translate_expr_to_conj(X, Conj, Value),
		     append(GsH, [he_once_visible_result(Conj, Value, Out)], Goals)
		; HV == once, he_profile_enabled
		  -> Out = [once|T],
		     Goals = GsH
		; HV == once, T = [X] -> translate_expr_to_conj(X, Conj, Out),
			                                 append(GsH, [once(Conj)], Goals)
		; HV == hyperpose, T = [L]
	  -> ( nonvar(L), is_list(L)
               -> build_hyperpose_branches(L, Branches),
                  append(GsH, [concurrent_and(member((Goal,Res), Branches),
                                                 he_hyperpose_branch_call(Goal, Res, Out))], Goals)
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
        ; HV == if, T = [Cond, Then] -> translate_expr_to_conj(Cond, ConC, Cv),
                                        translate_expr_to_conj(Then, ConT, Tv),
                                        build_branch(ConT, Tv, Out, BT),
                                        ( ConC == true -> append(GsH, [ ( Cv == true -> BT ) ], Goals)
                                                        ; append(GsH, [ ( ConC, ( Cv == true -> BT ) ) ], Goals) )
        ; HV == if, T = [Cond, Then, Else] -> translate_expr_to_conj(Cond, ConC, Cv),
                                              translate_expr_to_conj(Then, ConT, Tv),
                                              translate_expr_to_conj(Else, ConE, Ev),
                                              build_branch(ConT, Tv, Out, BT),
                                              build_branch(ConE, Ev, Out, BE),
                                              ( ConC == true -> append(GsH, [ (Cv == true -> BT ; BE) ], Goals)
                                                              ; append(GsH, [ (ConC, (Cv == true -> BT ; BE)) ], Goals) )
        ; HV == case, T = [KeyExpr, PairsExpr] -> ( select(Found0, PairsExpr, Rest0),
                                                    subsumes_term(['Empty', _], Found0),
                                                    Found0 = ['Empty', DefaultExpr],
                                                    NormalCases = Rest0
                                                     -> translate_expr_to_conj(KeyExpr, GkConj, Kv),
                                                       translate_case(NormalCases, Kv, Out, CaseGoal, KeyGoal),
                                                       translate_expr_to_conj(DefaultExpr, ConD, DOut),
                                                       build_branch(ConD, DOut, Out, DefaultThen),
                                                       ( GkConj == true
                                                       -> Combined = ( CaseGoal ; DefaultThen )
                                                       ;  Combined = ( GkConj, ( CaseGoal ; DefaultThen ) )
                                                       ),
                                                       append([GsH, KeyGoal, [Combined]], Goals)
                                                     ; translate_expr(KeyExpr, Gk, Kv),
                                                       translate_case(PairsExpr, Kv, Out, IfGoal, KeyGoal),
                                                       append([GsH, Gk, KeyGoal, [IfGoal]], Goals) )
        ; (HV == let ; HV == chain), T = [Pat, Val, In] -> translate_expr(Pat, Gp, Pv),
                                                           translate_expr(Val, Gv, V),
                                                           translate_expr(In,  Gi, Out),
                                                           append([GsH,[(Pv=V)],Gp,Gv,Gi], Goals)
        ; HV == 'let*', T = [Binds, Body] -> letstar_to_rec_let(Binds,Body,RecLet),
                                             translate_expr(RecLet,  Goals, Out)
        ; HV == sealed, T = [Vars, Expr], he_profile_enabled
          -> append(GsH, ['sealed'(Vars, Expr, Out)], Goals)
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
                                           % compile clause with all bound + free vars
                                           he_clause_functor(F, ClauseF),
                                           translate_clause([=, [F|FullArgs], Body], Clause, true, ClauseF),
                                           register_fun(F),
                                           assertz(Clause),
                                           format(atom(Label), "metta lambda (~w)", [F]),
                                           maybe_print_compiled_clause(Label, ['|->', Args, Body], Clause),
                                           length(FullArgs, N),
                                           Arity is N + 1,
                                           assertz(arity(F, Arity)),
                                           % emit closure capturing the environment (free vars)
                                           ( FreeVars == [] -> Out = F
                                                             ; Out = partial(F, FreeVars) )
        %--- Spaces ---:
        ; ( HV == 'add-atom' ; HV == 'remove-atom' ), T = [_,_] -> append(T, [Out], RawArgs),
                                                                   Goal =.. [HV|RawArgs],
                                                                   append(GsH, [Goal], Goals)
        ; HV == match, T = [Space, Pattern, Body], he_profile_enabled
          -> translate_expr(Space, G1, S),
             translate_expr_to_conj(Body, BodyConj, BodyOut),
             % Preserve the raw body term at the match boundary so HE match/4
             % can reject cyclic rational-tree captures before body evaluation.
             append(G1, [match(S, Pattern, Body, _), BodyConj, (Out = BodyOut)], Goals)
        ; HV == match, T = [Space, Pattern, Body] -> translate_expr(Space, G1, S),
                                                     translate_expr_to_conj(Body, BodyConj, BodyOut),
                                                     append(G1, [match(S, Pattern, _, _), BodyConj, (Out = BodyOut)], Goals)
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
                                     length(CallArgs, CallArity),
                                     call_clause_functor(F, CallArity, ClauseF),
                                     Goal =.. [ClauseF|CallArgs],
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
        ; HV == eval, T = [Arg] -> append(GsH, [], Inner),
                                   he_bridge_eval_goal(Arg, Out, Goal),
                                   append(Inner, [Goal], Goals)
        %Force arg to remain data/list:
        ; HV == quote, T = [Expr], he_profile_enabled
          -> append(GsH, [], Inner),
             Out = [quote, Expr],
             Goals = Inner
        ; HV == quote, T = [Expr] -> append(GsH, [], Inner),
                                     Out = Expr,
                                     Goals = Inner
        ; HV == 'catch', T = [Expr] ->
          translate_expr(Expr, GsExpr, ExprOut),
          append(GsH, [], Inner),
          goals_list_to_conj(GsExpr, Conj),
          Goal = catch((Conj, Out = ExprOut),
                       Exception,
                       (Exception = error(Type, Ctx) -> Out = ['Error', Type, Ctx]
                                                      ; Out = ['Error', Exception])),
          append(Inner, [Goal], Goals)
        ; he_post_builtin_dispatch(HV, T, GsH, Out, Goals)
        ; he_profile_enabled,
          he_dynamic_head_needs_raw_dispatch(HV),
          \+ ( is_list(H),
               \+ he_callable_data_head(H)
             )
          -> append(GsH, [he_dynamic_call_raw(HV, T, Out)], Goals)
        ; he_profile_enabled,
          atom(HV),
          he_symbolic_data_functor(HV)
          -> eval_data_list([HV|T], Gd, Out),
             append(GsH, Gd, Goals)
        %--- Automatic 'smart' dispatch, translator deciding when to create a predicate call, data list, or dynamic dispatch: ---
        ; translate_args_for_head(HV, T, GsT, AVs),
          %HE list-headed data tuple: preserve the head expression structurally,
          % but keep evaluating the remaining tuple elements.
          ( he_profile_enabled,
            is_list(H),
            \+ he_callable_data_head(H)
          -> eval_data_term(H, Gd, HV1),
             append(GsT, Gd, Goals),
             Out = [HV1|AVs]
          ; append(GsH, GsT, Inner),
            %Known function => direct call:
            ( is_list(AVs), 
            ( atom(HV), fun(HV), Fun = HV, AllAVs = AVs, IsPartial = false
            ; compound(HV), HV = partial(Fun, Bound), append(Bound,AVs,AllAVs), IsPartial = true
            ) % Check for type definition [:,HV,TypeChain]
            -> he_known_fun_dispatch(Fun, AllAVs, Out, Inner, T, GsH, IsPartial, Bound, Goals)
          ; he_unknown_or_callable_dispatch(HV, AVs, Out, Inner, Goals)
          %Literals (numbers, strings, etc.), known non-function atom => data:
          ; ( atomic(HV), \+ atom(HV) ; atom(HV), \+ fun(HV) ) -> Out = [HV|AVs],
                                                                  Goals = Inner
          %Plain data list: evaluate inner fun-sublists
          ; is_list(HV),
            he_profile_enabled
          -> append(Inner, [he_eval_or_reduce([HV|AVs], Out)], Goals)
          ; is_list(HV) -> eval_data_term(HV, Gd, HV1),
                           append(Inner, Gd, Goals),
                           Out = [HV1|AVs]
          %Unknown head (var/compound) => runtime dispatch:
                           ; append(Inner, [reduce([HV|AVs], Out)], Goals) )))).

%Generate actual function call or partial if arity not complete:
build_call_or_partial(Fun, AVs, Out, Inner, Extra, Goals) :- length(AVs, N),
                                                             Arity is N + 1,
                                                             ( maybe_specialize_call(Fun, AVs, Out, Goal)
                                                               -> append(Inner, [Goal|Extra], Goals)
                                                                ; ( ( current_predicate(Fun/Arity) ; catch(arity(Fun, Arity), _, fail) ),
                                                                     \+ ( current_op(_, _, Fun), Arity =< 2 ) )
                                                                  -> append(AVs, [Out], Args),
                                                                     Goal =.. [Fun|Args],
                                                                     append(Inner, [Goal|Extra], Goals)
                                                                   ; he_bridge_partial_or_data(Fun, AVs, Out),
                                                                     append(Inner, Extra, Goals) ).

%Type function call generation, returns function call plus typechecks for input and output:
typed_functioncall_branch(Fun, TypeChain, T, GsH, IsPartial, Bound, Out, BranchGoal) :-
    TypeChain = [->|Xs],
    append(ArgTypes, [OutType], Xs),
    translate_args_by_type(T, ArgTypes, GsT2, AVsTmp0),
    ( IsPartial -> append(Bound, AVsTmp0, AVsTmp) ; AVsTmp = AVsTmp0 ),
    append(GsH, GsT2, InnerTmp),
    ( (OutType == '%Undefined%' ; OutType == 'Atom')
       -> Extra = [] ; Extra = [('get-type'(Out, OutType) *-> true ; 'get-metatype'(Out, OutType))] ),
    build_call_or_partial(Fun, AVsTmp, Out, InnerTmp, Extra, GoalsList),
    goals_list_to_conj(GoalsList, BranchGoal).


%Selectively apply translate_args for non-Expression args while Expression args stay as data input:
translate_args_by_type([], _, [], []) :- !.
translate_args_by_type([A|As], [T|Ts], GsOut, [AV|AVs]) :-
                      ( T == 'Expression' -> AV = A, GsA = []
                                           ; translate_expr(A, GsA1, AV),
                                             ( (T == '%Undefined%' ; T == 'Atom')
                                               -> GsA = GsA1
                                                ; append(GsA1, [('get-type'(AV, T) *-> true ; 'get-metatype'(AV, T))], GsA))),
                                             translate_args_by_type(As, Ts, GsRest, AVs),
                                             append(GsA, GsRest, GsOut).

%Handle data list:
eval_data_term(X, [], X) :- (var(X); atomic(X)), !.
eval_data_term(Expr, Goals, Val) :-
    Expr = [Special|_],
    nonvar(Special),
    memberchk(Special, [quote, call]), !,
    translate_expr(Expr, Goals, Val).
eval_data_term([F|As], Goals, Val) :- he_bridge_eval_data_term([F|As], Goals, Val).
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

%Translate case expression recursively into nested if:
translate_case([[K,VExpr]|Rs], Kv, Out, Goal, KGo) :- translate_expr_to_conj(VExpr, ConV, VOut),
                                                      constrain_args(K, Kc, Gc),
                                                      build_branch(ConV, VOut, Out, Then),
                                                      ( Rs == [] -> Goal = ((Kv = Kc) -> Then), KGi=[]
                                                                  ; translate_case(Rs, Kv, Out, Next, KGi),
                                                                    Goal = ((Kv = Kc) -> Then ; Next) ),
                                                      append([Gc,KGi], KGo).

%Translate arguments recursively:
translate_args_for_head('=', Args, Goals, OutArgs) :-
    he_profile_enabled, !,
    translate_args(Args, Goals, OutArgs).
translate_args_for_head(Fun, Args, Goals, OutArgs) :-
    he_profile_enabled,
    atom(Fun),
    catch(nb_getval(Fun, Metas), _, fail),
    is_list(Metas),
    Metas \= [], !,
    translate_fun_args(Fun, Args, 1, Goals, OutArgs).
translate_args_for_head(_, Args, Goals, OutArgs) :-
    translate_args(Args, Goals, OutArgs).

translate_fun_args(_, [], _, [], []).
translate_fun_args(Fun, [Arg|Args], Index, Goals, [Out|OutArgs]) :-
    ( he_fun_arg_prefers_raw(Fun, Index, Arg)
    -> G1 = [],
       Out = Arg
    ;  translate_expr(Arg, G1, Out)
    ),
    Index1 is Index + 1,
    translate_fun_args(Fun, Args, Index1, G2, OutArgs),
    append(G1, G2, Goals).

he_fun_arg_prefers_raw(_Fun, _Index, Arg) :-
    he_profile_enabled,
    nonvar(Arg),
    is_list(Arg),
    Arg = [Head|_],
    atom(Head),
    he_constructor_symbol(Head), !.
he_fun_arg_prefers_raw(Fun, Index, Arg) :-
    catch(nb_getval(Fun, Metas), _, fail),
    member(fun_meta(PatternArgs, _), Metas),
    nth1(Index, PatternArgs, Pattern),
    he_fun_arg_raw_pattern(Pattern),
    he_fun_arg_is_data_surface(Arg), !.

he_fun_arg_raw_pattern(Pattern) :-
    nonvar(Pattern),
    is_list(Pattern),
    Pattern = [Head|_],
    atom(Head).

he_fun_arg_is_data_surface(Arg) :-
    var(Arg), !.
he_fun_arg_is_data_surface(Arg) :-
    atomic(Arg), !.
he_fun_arg_is_data_surface(Arg) :-
    is_list(Arg),
    Arg = [Head|_],
    ( var(Head)
    ; is_list(Head),
      \+ he_callable_data_head(Head)
    ; atom(Head),
      \+ fun(Head),
      \+ he_head_may_denote_callable(Head)
    ).

he_zero_arg_user_callable_atom(Head) :-
    atom(Head),
    \+ he_constructor_symbol(Head),
    ( he_has_zero_arg_atom_head_equation(Head)
    ; catch(nb_getval(Head, Metas), _, fail),
      is_list(Metas),
      Metas \= []
    ), !.

translate_args([], [], []).
translate_args([X|Xs], Goals, [V|Vs]) :- translate_expr(X, G1, V),
                                         translate_args(Xs, G2, Vs),
                                         append(G1, G2, Goals).

%Build A ; B ; C ... from a list:
disj_list([], fail).
disj_list([G], G).
disj_list([G|Gs], (G ; R)) :- disj_list(Gs, R).

%Build one disjunct per branch: (Conj, Out = Val):
build_superpose_branches([], _, []).
build_superpose_branches([E|Es], Out, [B|Bs]) :- translate_expr_to_conj(E, Conj, Val),
                                                 build_branch(Conj, Val, Out, B),
                                                 build_superpose_branches(Es, Out, Bs).

%Build hyperpose branch as a goal list for concurrent_maplist to consume:
build_hyperpose_branches([], []).
build_hyperpose_branches([E|Es], [(Goal, Res)|Bs]) :- translate_expr_to_conj(E, Goal, Res),
                                                      build_hyperpose_branches(Es, Bs).

build_hyperpose_once_branches([], _, []).
build_hyperpose_once_branches([E|Es], Out, [once(he_hyperpose_once_branch_call(Goal))|Bs]) :-
    translate_expr_to_conj(E, Conj, Val),
    build_branch(Conj, Val, Out, Goal),
    build_hyperpose_once_branches(Es, Out, Bs).

%Runtime hyperpose path for variable/computed list arguments.
hyperpose_runtime(Exprs, Out) :-
    is_list(Exprs),
    concurrent_and(member(Expr, Exprs), he_hyperpose_eval_expr(Expr, Out)).

he_hyperpose_eval_expr(Expr, Out) :-
    he_hyperpose_branch_call(eval(Expr, Out), Out, Out).

he_hyperpose_once_branch_call(Goal) :-
    he_hyperpose_branch_call(Goal, true, true).

:- dynamic he_hyperpose_thread_profile_enabled/0.
:- dynamic he_hyperpose_thread_profile_seq/1.
:- dynamic he_hyperpose_thread_profile_sample/6.

he_hyperpose_thread_profile_enable :-
    retractall(he_hyperpose_thread_profile_sample(_, _, _, _, _, _)),
    retractall(he_hyperpose_thread_profile_seq(_)),
    assertz(he_hyperpose_thread_profile_seq(0)),
    ( he_hyperpose_thread_profile_enabled -> true
    ; assertz(he_hyperpose_thread_profile_enabled)
    ).

he_hyperpose_thread_profile_disable :-
    retractall(he_hyperpose_thread_profile_enabled).

he_hyperpose_branch_call(Goal, Res, Out) :-
    he_hyperpose_thread_profile_enabled, !,
    he_hyperpose_profiled_branch_call(Goal, Res, Out).
he_hyperpose_branch_call(Goal, Res, Out) :-
    call(Goal),
    Out = Res.

he_hyperpose_profiled_branch_call(Goal, Res, Out) :-
    thread_self(Thread),
    he_hyperpose_goal_label(Goal, Label),
    get_time(Wall0),
    statistics(cputime, Cpu0),
    he_hyperpose_note_profile_sample(Thread, Label, Wall0, Wall0, Cpu0, Cpu0, start),
    catch(call(Goal), Error, he_hyperpose_profiled_error(Error, Thread, Label, Wall0, Cpu0)),
    get_time(Wall1),
    statistics(cputime, Cpu1),
    he_hyperpose_note_profile_sample(Thread, Label, Wall0, Wall1, Cpu0, Cpu1, success),
    Out = Res.

he_hyperpose_profiled_error(Error, Thread, Label, Wall0, Cpu0) :-
    get_time(Wall1),
    statistics(cputime, Cpu1),
    he_hyperpose_note_profile_sample(Thread, Label, Wall0, Wall1, Cpu0, Cpu1, error),
    throw(Error).

he_hyperpose_goal_label(Goal, Label) :-
    compound(Goal), !,
    functor(Goal, Name, Arity),
    format(atom(Label), '~w/~w', [Name, Arity]).
he_hyperpose_goal_label(Goal, Label) :-
    format(atom(Label), '~w', [Goal]).

he_hyperpose_note_profile_sample(Thread, Label, Wall0, Wall1, Cpu0, Cpu1, Status) :-
    WallMs is round((Wall1 - Wall0) * 1000),
    CpuMs is round((Cpu1 - Cpu0) * 1000),
    with_mutex(he_hyperpose_thread_profile,
               ( ( retract(he_hyperpose_thread_profile_seq(Id0))
                 -> Id is Id0 + 1
                 ;  Id = 1
                 ),
                 assertz(he_hyperpose_thread_profile_seq(Id))
               )),
    assertz(he_hyperpose_thread_profile_sample(Id, Thread, Label, WallMs, CpuMs, Status)).

he_hyperpose_thread_profile_report(Stream) :-
    aggregate_all(count, he_hyperpose_thread_profile_sample(_, _, _, _, _, _), Count),
    format(Stream, 'hyperpose_thread_samples=~w~n', [Count]),
    forall(he_hyperpose_thread_profile_sample(Id, Thread, Label, WallMs, CpuMs, Status),
           format(Stream, '~w\t~w\t~w\t~w\t~w\t~w~n',
                  [Id, Thread, Label, WallMs, CpuMs, Status])).

%Like membercheck but with direct equality rather than unification
memberchk_eq(V, [H|_]) :- V == H, !.
memberchk_eq(V, [_|T]) :- memberchk_eq(V, T).


%Generate readable lambda name:
next_lambda_name(Name) :- ( catch(nb_getval(lambda_counter, Prev), _, Prev = 0) ),
                          N is Prev + 1,
                          nb_setval(lambda_counter, N),
                          format(atom(Name), 'lambda_~d', [N]).
