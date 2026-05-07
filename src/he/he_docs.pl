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

'he_doc_lookup_item'(Item, Item) :-
    he_doc_atom(Item, _), !.
'he_doc_lookup_item'(Item0, Item) :-
    he_namespace_sugar_alias(Item0, Item),
    Item \== Item0,
    he_doc_atom(Item, _).

'get-doc'(Item, 'Empty') :-
    is_list(Item), !.
'get-doc'(Item0, 'Empty') :-
    \+ 'he_doc_lookup_item'(Item0, _), !.
'get-doc'(Item0, Doc) :-
    'he_doc_lookup_item'(Item0, Item),
    he_doc_atom(Item, Fields),
    'get-type'(Item, Type),
    he_doc_field(Fields, '@desc', "No documentation", Desc),
    he_doc_kind(Type, Fields, Kind),
    ( Kind == function
    -> he_doc_params_descs(Fields, ParamDescs),
       he_doc_function_parts(Type, ArgTypes, RetType),
       he_doc_formal_params(ArgTypes, ParamDescs, ParamsFormal),
       he_doc_return_desc(Fields, ReturnDesc),
       Doc = ['@doc-formal', ['@item', Item0], ['@kind', function], ['@type', Type],
              ['@desc', Desc], ['@params', ParamsFormal],
              ['@return', ['@type', RetType], ['@desc', ReturnDesc]]]
    ; Doc = ['@doc-formal', ['@item', Item0], ['@kind', atom], ['@type', Type], ['@desc', Desc]]
    ).

he_doc_text(Term, Text) :-
    string(Term), !,
    Text = Term.
he_doc_text(Term, Text) :-
    swrite(Term, Text).

he_doc_print_param(['@param', ['@type', Type], ['@desc', Desc]]) :-
    he_doc_text(Type, TypeText),
    he_doc_text(Desc, DescText),
    format("  ~w ~w~n", [TypeText, DescText]).

he_doc_print(['@doc-formal', ['@item', Item], ['@kind', function], ['@type', Type],
              ['@desc', Desc], ['@params', Params],
              ['@return', ['@type', RetType], ['@desc', ReturnDesc]]]) :-
    he_doc_text(Item, ItemText),
    he_doc_text(Type, TypeText),
    he_doc_text(Desc, DescText),
    he_doc_text(RetType, RetTypeText),
    he_doc_text(ReturnDesc, ReturnDescText),
    format("Function ~w: ~w ~w~n", [ItemText, TypeText, DescText]),
    format("Parameters:~n", []),
    forall(member(Param, Params), he_doc_print_param(Param)),
    format("Return: (type ~w) ~w~n", [RetTypeText, ReturnDescText]).
he_doc_print(['@doc-formal', ['@item', Item], ['@kind', function], ['@type', Type], ['@desc', Desc]]) :-
    he_doc_text(Item, ItemText),
    he_doc_text(Type, TypeText),
    he_doc_text(Desc, DescText),
    format("Function ~w: ~w ~w~n", [ItemText, TypeText, DescText]).
he_doc_print(['@doc-formal', ['@item', Item], ['@kind', atom], ['@type', Type], ['@desc', Desc]]) :-
    he_doc_text(Item, ItemText),
    he_doc_text(Type, TypeText),
    he_doc_text(Desc, DescText),
    format("Atom ~w: ~w ~w~n", [ItemText, TypeText, DescText]).
he_doc_print('Empty') :-
    format("No documentation found.~n", []).
he_doc_print(Other) :-
    he_doc_text(Other, Text),
    format("~w~n", [Text]).

'help!'(Item, []) :-
    once('get-doc'(Item, Doc)),
    he_doc_print(Doc).
