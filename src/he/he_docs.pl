he_doc_atom(Item, Fields) :-
    current_predicate('&self'/Arity),
    functor(Head, '&self', Arity),
    clause(Head, true),
    Head =.. ['&self'|Args],
    Args = ['@doc', Item | Fields].

he_doc_field(Fields, Name, Default, Value) :-
    ( member(Field, Fields),
      Field = [Name, V]
    -> Value = V
    ; Value = Default
    ).

he_doc_kind(Type, Fields, function) :-
    ( Type = [->|_]
    ; member(['@params', _], Fields)
    ; member(['@return', _], Fields)
    ), !.
he_doc_kind(_, _, atom).

he_doc_param_desc(['@param', Desc], Desc) :- !.
he_doc_param_desc(Desc, Desc).

he_doc_params_descs(Fields, Descs) :-
    ( member(['@params', Params], Fields),
      is_list(Params)
    -> maplist(he_doc_param_desc, Params, Descs)
    ; Descs = []
    ).

he_doc_return_desc(Fields, Desc) :-
    he_doc_field(Fields, '@return', '%Undefined%', Raw),
    ( Raw = ['@return', D] -> Desc = D ; Desc = Raw ).

he_doc_formal_params([], [], []).
he_doc_formal_params([Type|Types], [Desc|Descs], [[ '@param', ['@type', Type], ['@desc', Desc] ] | Out]) :-
    he_doc_formal_params(Types, Descs, Out).
he_doc_formal_params([Type|Types], [], [[ '@param', ['@type', Type], ['@desc', '%Undefined%'] ] | Out]) :-
    he_doc_formal_params(Types, [], Out).
he_doc_formal_params([], [Desc|Descs], [[ '@param', ['@type', '%Undefined%'], ['@desc', Desc] ] | Out]) :-
    he_doc_formal_params([], Descs, Out).

he_doc_function_parts(Type, ArgTypes, RetType) :-
    ( Type = [->|TypeItems],
      append(ArgTypes, [RetType], TypeItems)
    -> true
    ; ArgTypes = [],
      RetType = '%Undefined%'
    ).

'get-doc'(Item, 'Empty') :-
    is_list(Item), !.
'get-doc'(Item, 'Empty') :-
    \+ he_doc_atom(Item, _), !.
'get-doc'(Item, Doc) :-
    he_doc_atom(Item, Fields),
    'get-type'(Item, Type),
    he_doc_field(Fields, '@desc', "No documentation", Desc),
    he_doc_kind(Type, Fields, Kind),
    ( Kind == function
    -> he_doc_params_descs(Fields, ParamDescs),
       he_doc_function_parts(Type, ArgTypes, RetType),
       he_doc_formal_params(ArgTypes, ParamDescs, ParamsFormal),
       he_doc_return_desc(Fields, ReturnDesc),
       Doc = ['@doc-formal', ['@item', Item], ['@kind', function], ['@type', Type],
              ['@desc', Desc], ['@params', ParamsFormal],
              ['@return', ['@type', RetType], ['@desc', ReturnDesc]]]
    ; Doc = ['@doc-formal', ['@item', Item], ['@kind', atom], ['@type', Type], ['@desc', Desc]]
    ).

'help!'(Item, true) :-
    'get-doc'(Item, Doc),
    swrite(Doc, SDoc),
    format("~w~n", [SDoc]).

