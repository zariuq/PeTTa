% Proper fix: User spaces are stored in &self with space tags
% This keeps data separated while avoiding the '&kb'/3 predicate issue

% When matching in a user-defined space, wrap patterns with space tag
match(Space, Pattern, OutPattern, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|_]), !,
    % Wrap the pattern with a space tag
    TaggedPattern = [space_tag, Space, Pattern],
    match('&self', TaggedPattern, [space_tag, Space, OutPattern], Result).

% When adding to a user-defined space, wrap with space tag
'add-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|_]), !,
    % Wrap the atom with a space tag
    TaggedAtom = [space_tag, Space, Atom],
    'add-atom'('&self', TaggedAtom, Result).

% When removing from a user-defined space, wrap with space tag
'remove-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|_]), !,
    % Wrap the atom with a space tag
    TaggedAtom = [space_tag, Space, Atom],
    'remove-atom'('&self', TaggedAtom, Result).

% This way:
% - !(add-atom &kb (Color red))
%   becomes internally: add-atom('&self', [space_tag, '&kb', [Color, red]])
%
% - !(match &kb (Color $x) $x)
%   becomes internally: match('&self', [space_tag, '&kb', [Color, X]], [space_tag, '&kb', X])
%
% Each space's data remains separate!