% Fix for user-defined spaces in PeTTa
% The problem: User spaces like &kb are treated as literal atoms
% but there's no backing predicate storage for them

:- multifile match/4.
:- multifile 'add-atom'/3.
:- multifile 'remove-atom'/3.
:- multifile 'get-atoms'/2.

% When binding a new space, actually create the storage
'bind!'(SpaceName, ['new-space'], true) :-
    atom(SpaceName),
    atom_chars(SpaceName, ['&'|_]),
    % Register this as a valid user space
    assertz(user_space(SpaceName)),
    !.

% Override match for user-defined spaces
match(Space, Pattern, OutPattern, Result) :-
    user_space(Space), !,
    % Use Space as predicate name directly
    ( atom(Space) ->
        atom_string(Space, SpaceStr),
        % Remove the & prefix for the actual predicate name
        ( sub_string(SpaceStr, 1, _, 0, CleanName) ->
            atom_string(CleanSpace, CleanName)
        ; CleanSpace = Space
        ),
        match(CleanSpace, Pattern, OutPattern, Result)
    ; match('&self', Pattern, OutPattern, Result)
    ).

% Override add-atom for user-defined spaces
'add-atom'(Space, Atom, true) :-
    user_space(Space), !,
    % Redirect to &self or create dynamic predicate
    'add-atom'('&self', Atom, true).

% Make user spaces dynamic
:- dynamic user_space/1.