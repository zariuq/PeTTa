% Elegant fix: Convert user spaces to tagged subspaces in &self
% This maintains separation while using only the working &self space

% Override match for user-defined spaces
match(Space, Pattern, OutPattern, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|Rest]), !,
    atom_chars(SpaceName, Rest),
    % Convert to tagged pattern in &self
    match('&self', [subspace, SpaceName, Pattern], [subspace, SpaceName, OutPattern], Result).

% Override add-atom for user-defined spaces
'add-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|Rest]), !,
    atom_chars(SpaceName, Rest),
    % Convert to tagged atom in &self
    'add-atom'('&self', [subspace, SpaceName, Atom], Result).

% Override remove-atom for user-defined spaces
'remove-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|Rest]), !,
    atom_chars(SpaceName, Rest),
    % Convert to tagged atom in &self
    'remove-atom'('&self', [subspace, SpaceName, Atom], Result).

% Now &kb becomes (subspace kb ...) in &self
% Each space remains separate and everything works!