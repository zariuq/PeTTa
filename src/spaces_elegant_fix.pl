% Elegant fix: All user spaces are aliases for &self
% This maintains PeTTa's minimalist philosophy

% Add this single clause before the existing match/4 definitions:
% Any space that starts with & (except special ones) redirects to &self
match(Space, Pattern, OutPattern, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|_]), !,
    match('&self', Pattern, OutPattern, Result).

% Same for add-atom
'add-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|_]), !,
    'add-atom'('&self', Atom, Result).

% And remove-atom
'remove-atom'(Space, Atom, Result) :-
    atom(Space),
    Space \== '&self',
    Space \== '&mork',
    atom_chars(Space, ['&'|_]), !,
    'remove-atom'('&self', Atom, Result).

% This way, all user-defined spaces (&kb, &foo, etc.)
% automatically work by sharing &self's storage.
% Elegant, minimal, and fixes the issue!