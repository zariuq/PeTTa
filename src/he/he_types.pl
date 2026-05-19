% HE-facing type/evaluator support.
%
% This file follows the copied HE spec pipeline where the current corpus needs
% it: type discovery, function type applicability, match_types, type_cast, and
% metta/interpret_expression. The larger remaining audit target is the full
% bindings-threaded evaluator algorithm; keep additions here spec-shaped rather
% than growing the builtin table opportunistically.

:- dynamic 'get-type'/2.
:- dynamic he_type_fact/2.
:- dynamic he_function_typechains_cache/2.
:- dynamic he_function_typechains_arity_cache/3.
:- dynamic he_no_function_typechains/1.
:- dynamic he_no_function_typechain_arity/2.
:- dynamic he_pragma_interpreter_mode/1.

:- multifile 'get-metatype'/2.
:- multifile 'get-type'/2.
:- multifile 'is-expr'/2.
:- multifile 'is-space'/2.
:- multifile 'is-var'/2.

:- retractall(he_pragma_interpreter_mode(_)),
   assertz(he_pragma_interpreter_mode(default)).

%%% Type Discovery / get-type

get_function_type([F|Args], T) :-
    \+ he_profile_enabled,
    nonvar(F),
    match('&self', [':',F,[->|Ts]], _, _),
    append(As,[T],Ts),
    maplist('get-type',Args,As).
get_function_type([F|Args], T) :-
    he_profile_enabled,
    nonvar(F),
    he_function_type_term(F, FType),
    he_apply_function_type(FType, Args, T0),
    he_normalize_type_expr(T0, T).

'get-type'(X, T) :-
    he_profile_enabled, !,
    ( he_get_type_candidate(X, T)
    ; \+ he_get_type_candidate(X, _),
      \+ he_known_typed_expression(X),
      T = '%Undefined%' ).
'get-type'(X, T) :- (get_type_candidate(X, T) *-> true ; T = '%Undefined%' ).

he_get_type_candidate(X, 'Number')   :- number(X), !.
he_get_type_candidate(X, '%Undefined%') :- var(X), !.
he_get_type_candidate(X, 'String')   :- string(X), !.
he_get_type_candidate(true, 'Bool')  :- !.
he_get_type_candidate(false, 'Bool') :- !.
he_get_type_candidate('True', 'Bool')  :- !.
he_get_type_candidate('False', 'Bool') :- !.
he_get_type_candidate('&self', 'SpaceType') :- !.
he_get_type_candidate(X, T) :-
    he_bound_space_type(X, Raw),
    he_public_space_type(Raw, T), !.
he_get_type_candidate(X, T) :-
    atom(X),
    he_space_type(X, Raw),
    he_public_space_type(Raw, T), !.
he_get_type_candidate(X, 'Type') :- he_builtin_type_symbol(X), !.
he_get_type_candidate([=, A, B], '%Undefined%') :-
    'get-type'(A, TA),
    'get-type'(B, TB),
    TA \== '%Undefined%',
    TB \== '%Undefined%',
    TA == TB, !.
he_get_type_candidate([=, A, B], _) :-
    'get-type'(A, TA),
    'get-type'(B, TB),
    TA \== '%Undefined%',
    TB \== '%Undefined%',
    TA \== TB, !,
    fail.
he_get_type_candidate([=, _A, _B], '%Undefined%') :- !.
he_get_type_candidate(X, ['StateMonad', T]) :-
    he_space_ref_atom(X),
    catch(nb_getval(X, State), _, fail),
    he_state_handle(State, Id),
    state_cell(Id, T, _), !.
he_get_type_candidate(X, ['StateMonad', T]) :-
    he_state_handle(X, Id),
    state_cell(Id, T, _), !.
he_get_type_candidate(X, T) :- atom(X), he_builtin_type(X, T).
he_get_type_candidate(X, T) :-
    is_list(X), !,
    ( he_list_function_types(X, Types)
    -> member(T, Types)
    ; he_untyped_functor_application_type(X, T)
    -> true
    ; he_blocks_data_tuple_type_fallback(X)
    -> fail
    ; he_self_or_data_tuple_type(X, T)
    ).
he_get_type_candidate(X, T) :- get_function_type(X, T).
he_get_type_candidate(X, T) :- he_self_type_fact(X, T).

he_list_function_types([Fun|Args], Types) :-
    atom(Fun),
    !,
    \+ he_no_function_typechains(Fun),
    length(Args, Arity),
    \+ he_no_function_typechain_arity(Fun, Arity),
    he_function_typechains_for_arity(Fun, Arity, Matching),
    ( Matching == []
    -> assertz(he_no_function_typechain_arity(Fun, Arity)),
       fail
    ;  findall(Type,
               ( member(FType, Matching),
                 he_apply_list_function_type(FType, Args, Type)
               ),
               Types),
       Types \= []
    ).
he_list_function_types(X, Types) :-
    findall(Type, get_function_type(X, Type), Types),
    Types \= [].

get_type_candidate(X, 'Number')   :- number(X), !.
get_type_candidate(X, '%Undefined%') :- var(X), !.
get_type_candidate(X, 'String')   :- string(X), !.
get_type_candidate(true, 'Bool')  :- !.
get_type_candidate(false, 'Bool') :- !.
get_type_candidate('True', 'Bool')  :- !.
get_type_candidate('False', 'Bool') :- !.
get_type_candidate('&self', 'SpaceType') :- !.
get_type_candidate(X, T) :-
    he_profile_enabled,
    he_bound_space_type(X, Raw),
    he_public_space_type(Raw, T), !.
get_type_candidate(X, T) :-
    he_profile_enabled,
    atom(X),
    he_space_type(X, Raw),
    he_public_space_type(Raw, T), !.
get_type_candidate(X, 'Type') :- he_profile_enabled, he_builtin_type_symbol(X), !.
get_type_candidate([=, A, B], '%Undefined%') :-
    he_profile_enabled,
    'get-type'(A, TA),
    'get-type'(B, TB),
    TA \== '%Undefined%',
    TB \== '%Undefined%',
    TA == TB, !.
get_type_candidate([=, A, B], _) :-
    he_profile_enabled,
    'get-type'(A, TA),
    'get-type'(B, TB),
    TA \== '%Undefined%',
    TB \== '%Undefined%',
    TA \== TB, !,
    fail.
get_type_candidate([=, _A, _B], '%Undefined%') :-
    he_profile_enabled, !.
get_type_candidate(X, ['StateMonad', T]) :-
    he_profile_enabled,
    he_space_ref_atom(X),
    catch(nb_getval(X, State), _, fail),
    he_state_handle(State, Id),
    state_cell(Id, T, _), !.
get_type_candidate(X, ['StateMonad', T]) :-
    he_profile_enabled,
    he_state_handle(X, Id),
    state_cell(Id, T, _), !.
get_type_candidate(X, T) :- he_profile_enabled, atom(X), he_builtin_type(X, T).
get_type_candidate(X, T) :- he_profile_enabled, is_list(X), !,
                            ( he_list_function_types(X, Types)
                            -> member(T, Types)
                            ; he_untyped_functor_application_type(X, T)
                            -> true
                            ; he_blocks_data_tuple_type_fallback(X)
                            -> fail
                            ; he_self_or_data_tuple_type(X, T)
                            ).
get_type_candidate(X, T) :- get_function_type(X,T).
get_type_candidate(X, T) :- \+ he_profile_enabled,
                            \+ get_function_type(X, _),
                            is_list(X),
                            maplist('get-type', X, T).
get_type_candidate(X, T) :- he_self_type_fact(X, T).

'get-metatype'(X, 'Variable') :- var(X), !.
'get-metatype'(X, 'Grounded') :- number(X), !.
'get-metatype'(X, 'Grounded') :- string(X), !.
'get-metatype'(true,  'Grounded') :- !.
'get-metatype'(false, 'Grounded') :- !.
'get-metatype'(X, 'Grounded') :- he_ground_numeric_constant(X, _), !.
'get-metatype'(X, 'Grounded') :- atom(X), fun(X), !.
'get-metatype'(X, 'Expression') :- is_list(X), !.
'get-metatype'(X, 'Symbol') :- atom(X), !.

'is-var'(A,R) :- var(A) -> R=true ; R=false.
'is-expr'(A,R) :- is_list(A) -> R=true ; R=false.
'is-space'(A,[ 'is-space', A]) :-
    he_profile_enabled,
    is_list(A), !.
'is-space'(A,R) :- he_space_ref_atom(A) -> R=true ; R=false.

%%% Function Type Application

he_function_type_term(Fun, Type) :-
    \+ atom(Fun),
    he_non_atom_function_type(Fun, Type).
he_function_type_term(Fun, Type) :-
    atom(Fun),
    he_function_typechain(Fun, Type).

he_function_type_parts([->|TypeItems], ArgTypes, ReturnType) :-
    append(ArgTypes, [ReturnType], TypeItems).

he_arrow_typechain([->|_]).

he_non_atom_function_type(Fun, Type) :-
    he_self_type_fact(Fun, Type),
    he_arrow_typechain(Type).
he_non_atom_function_type(Fun, Type) :-
    he_non_atom_head_may_return_arrow(Fun),
    'get-type'(Fun, Type),
    he_arrow_typechain(Type).

he_non_atom_head_may_return_arrow([Head|Args]) :-
    atom(Head), !,
    length(Args, Arity),
    he_function_typechains_for_arity(Head, Arity, TypeChains),
    member(TypeChain, TypeChains),
    he_function_type_parts(TypeChain, _, ReturnType),
    he_possible_arrow_return_type(ReturnType), !.

he_possible_arrow_return_type(Type) :-
    var(Type), !.
he_possible_arrow_return_type([->|_]) :- !.
he_possible_arrow_return_type([':', _, Type]) :-
    he_possible_arrow_return_type(Type).

he_apply_function_type(FType, Args, T) :-
    ground(FType), !,
    he_function_type_parts(FType, ArgTypes, ReturnType),
    same_length(Args, ArgTypes),
    he_bind_argument_types(Args, ArgTypes),
    T = ReturnType.
he_apply_function_type(FType, Args, T) :-
    copy_term(FType-Args, FTypeCopy-ArgsCopy),
    he_function_type_parts(FTypeCopy, ArgTypesCopy, ReturnTypeCopy),
    same_length(ArgsCopy, ArgTypesCopy),
    he_bind_argument_types(ArgsCopy, ArgTypesCopy),
    copy_term(ReturnTypeCopy, T).

he_apply_list_function_type(FType, Args, Type) :-
    he_try_ground_function_type(FType, Args, Decision), !,
    Decision = type(T0),
    he_normalize_type_expr(T0, Type).
he_apply_list_function_type(FType, Args, Type) :-
    he_apply_function_type(FType, Args, T0),
    he_normalize_type_expr(T0, Type).

he_try_ground_function_type(FType, Args, Decision) :-
    ground(FType),
    he_function_type_parts(FType, ArgTypes, ReturnType),
    ( \+ same_length(Args, ArgTypes)
    -> Decision = mismatch
    ;  he_try_ground_arg_types(Args, ArgTypes, Decision0),
       ( Decision0 == match
       -> Decision = type(ReturnType)
       ;  Decision = mismatch
       )
    ).

he_try_ground_arg_types([], [], match).
he_try_ground_arg_types([Arg|Args], [Expected|Types], Decision) :-
    he_try_ground_arg_type(Arg, Expected, ArgDecision),
    ( ArgDecision == mismatch
    -> Decision = mismatch
    ;  he_try_ground_arg_types(Args, Types, Decision)
    ).

he_try_ground_arg_type(_, Expected, match) :-
    ( Expected == '%Undefined%'
    ; Expected == 'Atom'
    ), !.
he_try_ground_arg_type(Arg, Expected, Decision) :-
    var(Arg), !,
    ( he_meta_type(Expected)
    -> ( Expected == 'Variable' -> Decision = match ; Decision = mismatch )
    ;  Decision = match
    ).
he_try_ground_arg_type(Arg, Expected, Decision) :-
    he_fast_known_actual_type(Arg, Actual), !,
    ( he_match_types_live(Expected, Actual)
    -> Decision = match
    ;  Decision = mismatch
    ).
he_try_ground_arg_type(Arg, Expected, Decision) :-
    he_meta_type(Expected), !,
    ( 'get-metatype'(Arg, Expected)
    -> Decision = match
    ;  Decision = mismatch
    ).

he_fast_known_actual_type(Arg, 'Number') :-
    number(Arg), !.
he_fast_known_actual_type(Arg, 'String') :-
    string(Arg), !.
he_fast_known_actual_type(true, 'Bool') :- !.
he_fast_known_actual_type(false, 'Bool') :- !.
he_fast_known_actual_type('True', 'Bool') :- !.
he_fast_known_actual_type('False', 'Bool') :- !.
he_fast_known_actual_type('&self', 'SpaceType') :- !.

he_candidate_atom_type(Atom, Type) :-
    he_profile_enabled, !,
    he_get_type_candidate(Atom, Type).
he_candidate_atom_type(Atom, Type) :-
    get_type_candidate(Atom, Type).
he_candidate_atom_type(Atom, 'Type') :-
    he_profile_enabled,
    he_known_type_term(Atom).
he_candidate_atom_type(Atom, '%Undefined%') :-
    he_profile_enabled,
    \+ get_type_candidate(Atom, _),
    \+ he_known_typed_expression(Atom).

he_atom_types(Atom, ['Number']) :-
    number(Atom), !.
he_atom_types(Atom, ['String']) :-
    string(Atom), !.
he_atom_types(Atom, ['%Undefined%']) :-
    var(Atom), !.
he_atom_types(true, ['Bool']) :- !.
he_atom_types(false, ['Bool']) :- !.
he_atom_types('True', ['Bool']) :- !.
he_atom_types('False', ['Bool']) :- !.
he_atom_types('&self', ['SpaceType']) :- !.
he_atom_types(Atom, Types) :-
    findall(Type, he_candidate_atom_type(Atom, Type), Raw),
    alpha_list_to_set(Raw, Unique),
    ( Unique == []
    -> Types = ['%Undefined%']
    ; Types = Unique
    ).

he_self_or_data_tuple_type(X, T) :-
    once(he_self_type_fact(X, _)),
    he_self_type_fact(X, T).
he_self_or_data_tuple_type(X, T) :-
    is_list(X),
    maplist('get-type', X, T).

he_untyped_functor_application_type([Head, Elem], ['%Undefined%', ElemType]) :-
    atom(Head),
    'get-type'(Head, '%Undefined%'),
    'get-type'(Elem, ElemType),
    ElemType \== '%Undefined%'.
he_untyped_functor_application_type([Head, Elem, Tail], ['%Undefined%', ElemType]) :-
    atom(Head),
    'get-type'(Head, '%Undefined%'),
    'get-type'(Elem, ElemType),
    ElemType \== '%Undefined%',
    he_untyped_functor_tail_compatible(Tail, ElemType).

he_untyped_functor_tail_compatible([TailHead], _ElemType) :-
    atom(TailHead),
    'get-type'(TailHead, '%Undefined%').
he_untyped_functor_tail_compatible(Tail, ElemType) :-
    he_untyped_functor_application_type(Tail, ['%Undefined%', ElemType]).

he_blocks_data_tuple_type_fallback([Head|_]) :-
    he_head_may_denote_callable(Head), !.
he_blocks_data_tuple_type_fallback(List) :-
    member(Elem, List),
    is_list(Elem),
    Elem = [Head|_],
    atom(Head), !.

he_head_may_denote_callable(Head) :-
    is_list(Head),
    he_non_atom_head_may_return_arrow(Head), !.
he_head_may_denote_callable(Head) :-
    atom(Head),
    ( fun(Head)
    ; he_has_atom_head_equation(Head)
    ; he_has_zero_arg_atom_head_equation(Head)
    ; catch(nb_getval(Head, Metas), _, fail),
      is_list(Metas),
      Metas \= []
    ), !.
he_head_may_denote_callable(Head) :-
    atom(Head),
    he_function_typechains(Head, TypeChains),
    member(TypeChain, TypeChains),
    he_arrow_typechain(TypeChain), !.

he_self_type_fact(Subject, Type) :-
    he_profile_enabled, !,
    he_type_fact(Subject, Type).
he_self_type_fact(Subject, Type) :-
    match('&self', [':', Subject, Type], Type, _).

%%% match_types

he_match_types(Type1, Type2, Bindings, [Bindings]) :-
    he_match_types_live(Type1, Type2), !.
he_match_types(_, _, _, []).

he_match_types_live(Type1, Type2) :-
    nonvar(Type1),
    Type1 = [':', Binder, Expected], !,
    he_match_types_live(Expected, Type2),
    Binder = Type2.
he_match_types_live(Type1, Type2) :-
    nonvar(Type2),
    Type2 = [':', Binder, Expected], !,
    he_match_types_live(Type1, Expected),
    Binder = Type1.
he_match_types_live(Type1, Type2) :-
    he_space_type_compatible(Type1, Type2), !.
he_match_types_live(Type1, Type2) :-
    ( Type1 == '%Undefined%'
    ; Type1 == 'Atom'
    ; Type2 == '%Undefined%'
    ; Type2 == 'Atom'
    ), !.
he_match_types_live(Type1, Type2) :-
    is_list(Type1),
    is_list(Type2),
    same_length(Type1, Type2),
    maplist(he_match_types_live, Type1, Type2), !.
he_match_types_live(Type1, Type2) :-
    Type1 = Type2.

he_space_type_compatible('SpaceType', 'Space').
he_space_type_compatible('SpaceType', ['Space'|_]).
he_space_type_compatible('Space', 'SpaceType').
he_space_type_compatible(['Space'|_], 'SpaceType').
he_space_type_compatible('SpaceType', 'SpaceType').

%%% type_cast

he_type_cast(Atom, Bindings, Type, _Space, Results) :-
    he_meta_type(Type),
    'get-metatype'(Atom, ActualMeta),
    ( ActualMeta == Type
    -> Results = [(Atom, Bindings)]
    ; Results = [(['Error', Atom, ['BadType', Type, ActualMeta]], Bindings)]
    ), !.
he_type_cast(Atom, Bindings, Type, _Space, Results) :-
    he_untyped_zero_arity_constructor_cast(Atom, Bindings, Type, Results), !.
he_type_cast(Atom, Bindings, Type, _Space, Results) :-
    he_atom_types(Atom, Types),
    findall((Atom, MatchedBindings),
            ( member(ActualType, Types),
              copy_term(Type-ActualType, TypeCopy-ActualCopy),
              he_match_types(ActualCopy, TypeCopy, Bindings, Matches),
              member(MatchedBindings, Matches)
            ),
            Successes),
    ( Successes \= []
    -> Results = Successes
    ; findall((['Error', Atom, ['BadType', Type, ActualType]], Bindings),
              member(ActualType, Types),
              Errors0),
      ( Errors0 == []
      -> Results = [(['Error', Atom, ['BadType', Type, '%Undefined%']], Bindings)]
      ; Results = Errors0
      )
    ).

he_untyped_zero_arity_constructor_cast([Head], Bindings, Type, [([Head], Bindings)]) :-
    atom(Head),
    'get-type'(Head, '%Undefined%'),
    he_unknown_unary_constructor_type(Type).

he_unknown_unary_constructor_type(Type) :-
    he_strip_type_binder(Type, CoreType),
    nonvar(CoreType),
    CoreType = [FunctorType, _ElemType],
    he_type_is_fully_undefined_or_var(FunctorType).

he_strip_type_binder(Type, CoreType) :-
    nonvar(Type),
    Type = [':', _Binder, Inner], !,
    he_strip_type_binder(Inner, CoreType).
he_strip_type_binder(Type, Type).

he_type_is_fully_undefined_or_var(Type) :-
    var(Type), !.
he_type_is_fully_undefined_or_var(Type) :-
    he_type_is_fully_undefined(Type).

%%% metta / interpret_expression

he_metta(Atom, Type, _Space, Bindings, Results) :-
    he_metta_raw_result(Atom, Type, Bindings, Results), !.
he_metta(Atom, Type, Space, Bindings, Results) :-
    he_metta_casts_without_interpretation(Atom, Type), !,
    he_type_cast(Atom, Bindings, Type, Space, Results).
he_metta(Atom, Type, Space, Bindings, Results) :-
    he_interpret_expression(Atom, Type, Space, Bindings, Results0),
    include(he_success_pair, Results0, Successes),
    ( Successes \= []
    -> Results = Successes
    ; Results = Results0
    ).

he_metta_one(Atom, Type, _Space, Out) :-
    he_metta_raw_result(Atom, Type, [], Results), !,
    member((Out, _), Results).
he_metta_one(Atom, Type, Space, Out) :-
    he_metta_casts_without_interpretation(Atom, Type), !,
    he_type_cast(Atom, [], Type, Space, Results),
    member((Out, _), Results).
he_metta_one(Atom, Type, Space, Out) :-
    he_metta_success_value(Atom, Type, Space, Out).
he_metta_one(Atom, Type, Space, Out) :-
    \+ he_metta_has_success_value(Atom, Type, Space),
    he_metta_any_value(Atom, Type, Space, Out).
he_metta_one(Atom, _Type, Space, []) :-
    \+ he_metta_has_any_eval_value(Atom, Space).

he_evalc_one(Atom, Space0, Out) :-
    he_profile_enabled,
    he_space_ref_atom(Space0),
    \+ he_actual_space_target(Space0, _), !,
    swrite([evalc, Atom, Space0], Found),
    format(atom(Msg), 'expected: (evalc <atom> <space>), found: ~w', [Found]),
    Out = ['Error', [evalc, Atom, Space0], Msg].
he_evalc_one(Atom, Space0, Out) :-
    he_resolve_space_ref(Space0, Space),
    he_evalc_in_space(Atom, Space, Out).

he_evalc_in_space(Atom, '&self', Out) :-
    !,
    he_metta_one(Atom, '%Undefined%', '&self', Out).
he_evalc_in_space(Atom, Space, Out) :-
    he_evalc_space_equation(Space, Atom, Out), !.
he_evalc_in_space(Atom, _Space, Out) :-
    he_metta_one(Atom, '%Undefined%', '&self', Out).

he_evalc_space_equation(Space, Atom, Out) :-
    is_list(Atom),
    catch(match(Space, [=, Atom, Body], Body, _), _, fail), !,
    he_evalc_in_space(Body, Space, Out).
he_evalc_space_equation(Space, Atom, Out) :-
    atom(Atom),
    catch(match(Space, [=, Atom, Body], Body, _), _, fail), !,
    he_evalc_in_space(Body, Space, Out).

he_metta_raw_result(Atom, _Type, Bindings, [(Atom, Bindings)]) :-
    nonvar(Atom),
    Atom = ['Error'|_], !.
he_metta_raw_result(Atom, Type, Bindings, [(Atom, Bindings)]) :-
    ( Type == 'Atom'
    ; 'get-metatype'(Atom, Type)
    ; 'get-metatype'(Atom, 'Variable')
    ), !.

he_metta_casts_without_interpretation(Atom, _Type) :-
    Atom == [], !.
he_metta_casts_without_interpretation(Atom, _Type) :-
    'get-metatype'(Atom, Meta),
    ( Meta == 'Symbol'
    ; Meta == 'Grounded'
    ).

he_interpret_expression(Atom, Type, Space, Bindings, Results) :-
    findall((Out, Bindings),
            ( he_eval_in_space_for_metta(Atom, Space, Raw),
              he_cast_result(Atom, Type, Raw, Out)
            ),
            RawResults),
    ( RawResults == []
    -> Results = [([], Bindings)]
    ; Results = RawResults
    ).

he_eval_in_space_for_metta(Atom, '&self', Raw) :-
    !,
    catch(he_eval_special(Atom, EvalRaw), _, fail),
    he_metta_eval_special_raw(Atom, EvalRaw, Raw).
he_eval_in_space_for_metta(Atom, Space, Raw) :-
    he_evalc_in_space(Atom, Space, Raw).

he_metta_eval_special_raw(Atom, [eval, Atom], Atom) :- !.
he_metta_eval_special_raw(Atom, [quote, Atom], Atom) :- !.
he_metta_eval_special_raw(_Atom, EvalRaw, EvalRaw).

he_metta_success_value(Atom, Type, Space, Out) :-
    he_eval_in_space_for_metta(Atom, Space, Raw),
    he_cast_result(Atom, Type, Raw, Out),
    \+ he_error_atom(Out).

he_metta_has_success_value(Atom, Type, Space) :-
    once(he_metta_success_value(Atom, Type, Space, _)).

he_metta_any_value(Atom, Type, Space, Out) :-
    he_eval_in_space_for_metta(Atom, Space, Raw),
    he_cast_result(Atom, Type, Raw, Out).

he_metta_has_any_eval_value(Atom, Space) :-
    once(he_eval_in_space_for_metta(Atom, Space, _)).

he_success_pair((Atom, _)) :-
    \+ he_error_atom(Atom).

he_error_atom(Atom) :-
    nonvar(Atom),
    Atom = [Head|_],
    nonvar(Head),
    Head == 'Error'.

%%% Function Applicability / Argument Errors

he_argument_matches_expected(Argument, ExpectedType) :-
    nonvar(ExpectedType),
    ExpectedType == 'Expression',
    is_list(Argument), !.
he_argument_matches_expected(Argument, ExpectedType) :-
    nonvar(ExpectedType),
    he_meta_type(ExpectedType), !,
    'get-metatype'(Argument, ExpectedType).
he_argument_matches_expected(Argument, ExpectedType) :-
    he_atom_types(Argument, ActualTypes),
    member(ActualType, ActualTypes),
    ( he_match_types_live(ExpectedType, ActualType)
    ; he_type_is_fully_undefined(ActualType)
    ).

he_check_argument_type(Argument, ExpectedType, _Space, Bindings, Results) :-
    he_atom_types(Argument, ActualTypes),
    findall(Result,
            ( member(ActualType, ActualTypes),
              copy_term(ExpectedType-ActualType-Bindings,
                        ExpectedCopy-ActualCopy-BindingsCopy),
              he_match_types(ExpectedCopy, ActualCopy, BindingsCopy, Matches),
              ( Matches == [],
                \+ he_type_is_fully_undefined(ActualType)
              -> Result = err(ActualType)
              ;  ( Matches == []
                 -> MatchedBindings = Bindings
                 ;  member(MatchedBindings, Matches)
                 ),
                 Result = ok(MatchedBindings)
              )
            ),
            Results).

he_bind_argument_types([], []).
he_bind_argument_types([Argument|Args], [ExpectedType|Types]) :-
    he_bind_argument_type(Argument, ExpectedType),
    he_bind_argument_types(Args, Types).

he_bind_argument_type(Argument, BinderType) :-
    nonvar(BinderType),
    BinderType = [':', Binder, ExpectedType],
    !,
    he_bind_argument_type(Argument, ExpectedType),
    Binder = Argument.
he_bind_argument_type(Argument, ExpectedType) :-
    he_argument_matches_expected(Argument, ExpectedType).

he_argument_binding_error([Argument|_], [ExpectedType|_], Index, Index, ExpectedType, ActualType) :-
    \+ he_bind_argument_type(Argument, ExpectedType),
    he_first_bad_actual_type(Argument, ExpectedType, ActualType), !.
he_argument_binding_error([Argument|Args], [ExpectedType|Types], Index0, Index, ExpectedOut, ActualOut) :-
    he_bind_argument_type(Argument, ExpectedType),
    Index1 is Index0 + 1,
    he_argument_binding_error(Args, Types, Index1, Index, ExpectedOut, ActualOut).

he_first_bad_actual_type(Argument, ExpectedType, ActualType) :-
    he_atom_types(Argument, ActualTypes),
    \+ ( member(ActualMatch, ActualTypes),
         copy_term(ExpectedType-ActualMatch, ExpectedCopy-ActualCopy),
         he_match_types_live(ExpectedCopy, ActualCopy)
       ),
    member(ActualType, ActualTypes), !.
he_first_bad_actual_type(_, _, '%Undefined%').

he_check_if_function_type_is_applicable(Atom, FuncType, ExpectedType, _Space, [], Result) :-
    ground(FuncType),
    ground(ExpectedType),
    Atom = [_|Args],
    ground(Args),
    he_try_ground_function_type(FuncType, Args, type(ReturnType)), !,
    he_match_types(ExpectedType, ReturnType, [], ReturnMatches),
    ( ReturnMatches == []
    -> Result = err([['Error', Atom, ['BadType', ExpectedType, ReturnType]]])
    ;  Result = ok([ReturnType])
    ).
he_check_if_function_type_is_applicable(Atom, FuncType, ExpectedType, Space, [], Result) :-
    ground(FuncType),
    ground(ExpectedType),
    Atom = [_|Args],
    ground(Args), !,
    he_function_type_parts(FuncType, ArgTypes, ReturnType),
    ( \+ same_length(Args, ArgTypes)
    -> Result = err([['Error', Atom, 'IncorrectNumberOfArguments']])
    ;  he_check_function_args(Atom, Args, ArgTypes, Space, [], 1, ArgErrors),
       ( ArgErrors \= []
       -> Result = err(ArgErrors)
       ;  he_match_types(ExpectedType, ReturnType, [], ReturnMatches),
          ( ReturnMatches == []
          -> Result = err([['Error', Atom, ['BadType', ExpectedType, ReturnType]]])
          ;  Result = ok([ReturnType])
          )
       )
    ).
he_check_if_function_type_is_applicable(Atom, FuncType, ExpectedType, Space, Bindings, Result) :-
    Atom = [_|Args],
    copy_term(FuncType-ExpectedType-Args-Bindings,
              FuncCopy-ExpectedCopy-ArgsCopy-BindingsCopy),
    he_function_type_parts(FuncCopy, ArgTypesCopy, ReturnTypeCopy),
    ( \+ same_length(ArgsCopy, ArgTypesCopy)
    -> Result = err([['Error', Atom, 'IncorrectNumberOfArguments']])
    ;  he_check_function_args(Atom, ArgsCopy, ArgTypesCopy, Space, BindingsCopy, 1, ArgErrors),
       ( ArgErrors \= []
       -> Result = err(ArgErrors)
       ;  he_match_types(ExpectedCopy, ReturnTypeCopy, BindingsCopy, ReturnMatches),
          ( ReturnMatches == []
          -> copy_term(ExpectedCopy-ReturnTypeCopy, ExpectedOut-ActualOut),
             Result = err([['Error', Atom, ['BadType', ExpectedOut, ActualOut]]])
          ;  copy_term(ReturnTypeCopy, ReturnType),
             Result = ok([ReturnType])
          )
       )
    ).

he_check_function_args(_, [], [], _, _, _, []).
he_check_function_args(Atom, [Arg|Args], [Expected|Types], Space, Bindings, Index, Errors) :-
    ( he_bind_argument_type(Arg, Expected)
    -> Index1 is Index + 1,
       he_check_function_args(Atom, Args, Types, Space, Bindings, Index1, Errors)
    ;  he_check_argument_type(Arg, Expected, Space, Bindings, Checks),
       findall(Error,
               ( member(err(Actual), Checks),
                 copy_term(Expected-Actual, ExpectedOut-ActualOut),
                 Error = ['Error', Atom, ['BadArgType', Index, ExpectedOut, ActualOut]]
               ),
               RawErrors),
       alpha_list_to_set(RawErrors, Errors)
    ).

%%% Type Normalization

he_normalize_type_expr(T, T) :-
    var(T), !.
he_normalize_type_expr(T, T) :-
    atomic(T), !.
he_normalize_type_expr([F|Args], Out) :-
    maplist(he_normalize_type_expr, Args, NormArgs),
    ( he_eval_numeric_type_expr(F, NormArgs, EvalOut)
    -> Out = EvalOut
    ; Out = [F|NormArgs]
    ).

he_eval_numeric_type_expr('+', [A, B], Out) :-
    number(A), number(B), !,
    Out is A + B.
he_eval_numeric_type_expr('-', [A, B], Out) :-
    number(A), number(B), !,
    Out is A - B.
he_eval_numeric_type_expr('*', [A, B], Out) :-
    number(A), number(B), !,
    Out is A * B.
he_eval_numeric_type_expr('/', [A, B], Out) :-
    number(A), number(B), B =\= 0, !,
    Out is A / B.
he_eval_numeric_type_expr('%', [A, B], Out) :-
    number(A), number(B), B =\= 0, !,
    Out is A mod B.

%%% Builtin Type Inventory

he_builtin_type_symbol('Number').
he_builtin_type_symbol('Bool').
he_builtin_type_symbol('String').
he_builtin_type_symbol('Type').
he_builtin_type_symbol('Atom').
he_builtin_type_symbol('Symbol').
he_builtin_type_symbol('Expression').
he_builtin_type_symbol('Grounded').
he_builtin_type_symbol('Variable').
he_builtin_type_symbol('SpaceType').
he_builtin_type_symbol('Space').
he_builtin_type_symbol('MorkSpace').
he_builtin_type_symbol('StateMonad').

he_ground_numeric_constant('PI', 3.141592653589793).
he_ground_numeric_constant('EXP', 2.718281828459045).

he_builtin_type('+', [->, 'Number', 'Number', 'Number']).
he_builtin_type('-', [->, 'Number', 'Number', 'Number']).
he_builtin_type('*', [->, 'Number', 'Number', 'Number']).
he_builtin_type('/', [->, 'Number', 'Number', 'Number']).
he_builtin_type('%', [->, 'Number', 'Number', 'Number']).
he_builtin_type('<', [->, 'Number', 'Number', 'Bool']).
he_builtin_type('>', [->, 'Number', 'Number', 'Bool']).
he_builtin_type('<=', [->, 'Number', 'Number', 'Bool']).
he_builtin_type('>=', [->, 'Number', 'Number', 'Bool']).
he_builtin_type('==', TypeChain) :-
    he_auto_typecheck(true), !,
    TypeChain = [->, T, T, 'Bool'].
he_builtin_type('==', [->, 'Atom', 'Atom', 'Bool']) :-
    he_auto_typecheck(false).
he_builtin_type('!=', TypeChain) :-
    he_auto_typecheck(true), !,
    TypeChain = [->, T, T, 'Bool'].
he_builtin_type('!=', [->, 'Atom', 'Atom', 'Bool']) :-
    he_auto_typecheck(false).
he_builtin_type(and, [->, 'Bool', 'Bool', 'Bool']).
he_builtin_type(or, [->, 'Bool', 'Bool', 'Bool']).
he_builtin_type(xor, [->, 'Bool', 'Bool', 'Bool']).
he_builtin_type(implies, [->, 'Bool', 'Bool', 'Bool']).
he_builtin_type(not, [->, 'Bool', 'Bool']).
he_builtin_type('get-type', [->, 'Atom', 'Type']).
he_builtin_type('get-metatype', [->, 'Atom', 'Symbol']).
he_builtin_type('new-state', [->, T, ['StateMonad', T]]).
he_builtin_type('get-state', [->, ['StateMonad', T], T]).
he_builtin_type('change-state!', [->, ['StateMonad', T], T, ['StateMonad', T]]).
he_builtin_type('system-cwd', [->, 'String']).
he_builtin_type('system-has-args', [->, 'Bool']).
he_builtin_type('PI', 'Number').
he_builtin_type('EXP', 'Number').

he_invalidate_all_function_typechain_cache :-
    retractall(he_function_typechains_cache(_, _)),
    retractall(he_function_typechains_arity_cache(_, _, _)),
    retractall(he_no_function_typechains(_)),
    retractall(he_no_function_typechain_arity(_, _)).

he_invalidate_function_typechain_cache(Fun) :-
    atom(Fun), !,
    retractall(he_function_typechains_cache(Fun, _)),
    retractall(he_function_typechains_arity_cache(Fun, _, _)),
    retractall(he_no_function_typechains(Fun)),
    retractall(he_no_function_typechain_arity(Fun, _)).
he_invalidate_function_typechain_cache(_).

he_space_fact_added_hook('&self', [':', Subject, Type]) :-
    !,
    ( he_type_fact_variant(Subject, Type)
    -> true
    ; assertz(he_type_fact(Subject, Type))
    ),
    he_invalidate_type_fact_subject(Subject).

he_space_fact_removed_hook('&self', [':', Subject, Type]) :-
    !,
    he_retract_type_fact_variant(Subject, Type),
    he_invalidate_type_fact_subject(Subject).

he_type_fact_variant(Subject, Type) :-
    he_type_fact(StoredSubject, StoredType),
    StoredSubject =@= Subject,
    StoredType =@= Type, !.

he_retract_type_fact_variant(Subject, Type) :-
    forall((clause(he_type_fact(StoredSubject, StoredType), true, Ref),
            StoredSubject =@= Subject,
            StoredType =@= Type),
           erase(Ref)).

he_invalidate_type_fact_subject(Subject) :-
    atom(Subject), !,
    he_invalidate_function_typechain_cache(Subject).
he_invalidate_type_fact_subject(_) :-
    he_invalidate_all_function_typechain_cache.

he_function_typechain_uncached(Fun, TypeChain) :-
    he_type_fact(Fun, TypeChain).
he_function_typechain_uncached(Fun, TypeChain) :-
    \+ he_profile_enabled,
    catch(match('&self', [':', Fun, TypeChain], TypeChain, TypeChain), _, fail),
    \+ he_type_fact(Fun, TypeChain).
he_function_typechain_uncached(Fun, TypeChain) :-
    he_profile_enabled,
    he_builtin_type(Fun, TypeChain).

he_function_typechain(Fun, TypeChain) :-
    atom(Fun), !,
    he_function_typechains(Fun, TypeChains),
    member(TypeChain, TypeChains).
he_function_typechain(Fun, TypeChain) :-
    he_function_typechain_uncached(Fun, TypeChain).

he_function_typechains(Fun, TypeChains) :-
    atom(Fun),
    he_function_typechains_cache(Fun, TypeChains), !.
he_function_typechains(Fun, TypeChains) :-
    atom(Fun), !,
    findall(TypeChain, he_function_typechain_uncached(Fun, TypeChain), Raw),
    alpha_list_to_set(Raw, TypeChains),
    assertz(he_function_typechains_cache(Fun, TypeChains)).
he_function_typechains(Fun, TypeChains) :-
    findall(TypeChain, he_function_typechain_uncached(Fun, TypeChain), Raw),
    alpha_list_to_set(Raw, TypeChains).

he_function_typechains_for_arity(Fun, _Arity, TypeChains) :-
    he_no_function_typechains(Fun), !,
    TypeChains = [].
he_function_typechains_for_arity(Fun, Arity, TypeChains) :-
    he_function_typechains_arity_cache(Fun, Arity, TypeChains), !.
he_function_typechains_for_arity(Fun, Arity, TypeChains) :-
    he_function_typechains(Fun, AllTypeChains),
    ( AllTypeChains == []
    -> assertz(he_no_function_typechains(Fun)),
       TypeChains = []
    ;  include(he_typechain_arity_matches_arity(Arity), AllTypeChains, TypeChains),
       assertz(he_function_typechains_arity_cache(Fun, Arity, TypeChains))
    ).

he_known_typed_expression(X) :-
    is_list(X),
    X = [=, A, B], !,
    'get-type'(A, TA),
    TA \== '%Undefined%',
    'get-type'(B, TB),
    TB \== '%Undefined%'.
he_known_typed_expression(X) :-
    is_list(X),
    X = [Fun|_],
    ( atom(Fun),
      he_function_typechains(Fun, TypeChains),
      TypeChains \= []
    ; 'get-type'(Fun, FunType),
      FunType = [->|_]
    ).

he_eval_if_expr(X, V) :-
    ( is_list(X)
    -> eval(X, V)
    ; V = X ).

'pragma!'('type-check', auto, []) :-
    retractall(he_auto_typecheck(_)),
    assertz(he_auto_typecheck(true)),
    he_invalidate_all_function_typechain_cache, !.
'pragma!'('type-check', off, []) :-
    retractall(he_auto_typecheck(_)),
    assertz(he_auto_typecheck(false)),
    he_invalidate_all_function_typechain_cache, !.
'pragma!'(dialect, mettail, []) :- !.
'pragma!'(interpreter, 'bare-minimal', []) :-
    retractall(he_pragma_interpreter_mode(_)),
    assertz(he_pragma_interpreter_mode('bare-minimal')), !.
'pragma!'('max-stack-depth', Depth, []) :-
    integer(Depth),
    Depth >= 0,
    \+ he_pragma_interpreter_mode('bare-minimal'), !.
'pragma!'('search-table-mode', variant, []) :-
    \+ he_pragma_interpreter_mode('bare-minimal'), !.
'pragma!'(Key, Value, ['pragma!', Key, Value]).

%%% Runtime Type Helpers

he_typechain_arity_matches(Args, [->|TypeItems]) :-
    append(ArgTypes, [_], TypeItems),
    same_length(Args, ArgTypes).

he_typechain_arity_matches_arity(Arity, [->|TypeItems]) :-
    length(TypeItems, TypeItemCount),
    TypeItemCount =:= Arity + 1.

he_args_type_error(Args, ExpectedTypes, _Index, Error) :-
    copy_term(Args-ExpectedTypes, ArgsCopy-ExpectedCopy),
    he_argument_binding_error(ArgsCopy, ExpectedCopy, 1, BadIndex, Expected, Actual),
    copy_term(Expected-Actual, ExpectedOut-ActualOut),
    Error = ['BadArgType', BadIndex, ExpectedOut, ActualOut].

he_first_error_arg([Arg|_], Arg) :-
    nonvar(Arg),
    Arg = [Tag|_],
    Tag == 'Error', !.
he_first_error_arg([_|Args], Error) :-
    he_first_error_arg(Args, Error).

he_args_have_undefined([Arg|Args], [_|Types]) :-
    ( he_arg_has_undefined_type(Arg)
    ; he_args_have_undefined(Args, Types)
    ).
he_args_have_undefined([], []) :- fail.

he_args_have_runtime_undefined([Arg|_]) :-
    he_arg_has_undefined_type(Arg), !.
he_args_have_runtime_undefined([_|Args]) :-
    he_args_have_runtime_undefined(Args).
he_args_have_runtime_undefined([]) :-
    fail.

he_arg_has_undefined_type(Arg) :-
    he_atom_types(Arg, Types),
    member(Type, Types),
    he_type_is_fully_undefined(Type), !.

he_args_include_data_type([Type|_]) :-
    nonvar(Type),
    ( Type == 'Atom'
    ; Type == 'Expression'
    ), !.
he_args_include_data_type([_|Types]) :-
    he_args_include_data_type(Types).

he_type_accepts(BinderType, Arg, Actual) :-
    nonvar(BinderType),
    BinderType = [':', Binder, Expected], !,
    he_type_accepts(Expected, Arg, Actual),
    Binder = Arg.
he_type_accepts(Expected, Arg, Actual) :-
    copy_term(Expected-Arg, ExpectedCopy-ArgCopy),
    he_argument_matches_expected(ArgCopy, ExpectedCopy), !,
    he_actual_type(Arg, Actual).
he_type_accepts(_, Arg, Actual) :-
    he_actual_type(Arg, Actual),
    he_type_is_fully_undefined(Actual), !.

he_type_is_fully_undefined('%Undefined%').
he_type_is_fully_undefined([Type|Types]) :-
    he_type_is_fully_undefined(Type),
    he_type_list_fully_undefined(Types).

he_type_list_fully_undefined([]).
he_type_list_fully_undefined([Type|Types]) :-
    he_type_is_fully_undefined(Type),
    he_type_list_fully_undefined(Types).

he_cast_result(_, Expected, Value, Value) :-
    ( var(Expected)
    ; Expected == '%Undefined%'
    ; Expected == 'Atom'
    ), !.
he_cast_result(_, Expected, Value, Value) :-
    he_type_cast(Value, [], Expected, '&self', Results),
    member((Value, _), Results), !.
he_cast_result(Atom, Expected, Value, ['Error', Atom, ['BadType', Expected, Actual]]) :-
    he_first_bad_actual_type(Value, Expected, Actual).

he_meta_type('Symbol').
he_meta_type('Variable').
he_meta_type('Expression').
he_meta_type('Grounded').

he_known_type_term([->|_]).
he_known_type_term(['Space'|_]).
he_known_type_term(['MorkSpace'|_]).
he_known_type_term(['StateMonad'|_]).
he_known_type_term(Type) :-
    atom(Type),
    ( he_builtin_type_symbol(Type)
    ; catch(match('&self', [':', _, Type], _, _), _, fail)
    ).

he_actual_type(Arg, Type) :-
    ( 'get-type'(Arg, T), T \== '%Undefined%' -> Type = T
    ; he_profile_enabled ->
        ( var(Arg)
        -> Type = '%Undefined%'
        ; he_known_type_term(Arg)
        -> Type = 'Type'
        ; 'get-metatype'(Arg, Meta),
          ( Meta == 'Variable' -> Type = '%Undefined%' ; Type = Meta ) )
    ; 'get-metatype'(Arg, Type) ).

he_public_space_type('Space', 'SpaceType').
he_public_space_type(['Space'|_], 'SpaceType').
he_public_space_type(Type, Type).
