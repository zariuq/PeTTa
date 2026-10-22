:- ensure_loaded('../src/metta').

:- begin_tests(syntax_heads).

% The heads translate_expr/3 dispatches on: the atoms its clause compares the
% head's value with (the variable compared with reduce).
dispatched(Hs) :- findall(H, ( clause(translate_expr(_, _, _), B), head_value(B, X), compared(B, X, H) ), Hs0),
                  sort(Hs0, Hs).
head_value(B, X) :- sub_term(S, B), compound(S), S = (X == R), var(X), R == reduce, !.
compared(B, X, H) :- sub_term(S, B), compound(S),
                     ( S = (Y == H) ; S = memberchk(Y, L), is_list(L), member(H, L) ),
                     Y == X, atom(H).

% The heads rewrite_streamops/2 rewrites.
rewritten(Hs) :- findall(H, ( clause(rewrite_streamops(P, _), _), nonvar(P), P = [H|_], atom(H) ), Hs0),
                 sort(Hs0, Hs).

test(dispatch_found, [true(length(Hs, N)), true(N > 30)]) :- dispatched(Hs).

test(table_covers_dispatch, Missing == []) :-
        dispatched(D), rewritten(R), append(D, R, All),
        exclude(syntax_head, All, Missing).

test(table_has_no_stale_entries, Stale == []) :-
        dispatched(D), rewritten(R), syntax_heads(Table),
        exclude({D, R}/[H]>>( memberchk(H, D) ; memberchk(H, R) ), Table, Stale).

% A function or a data symbol is no syntax head.
test(functions_are_not_syntax) :- \+ syntax_head('+'), \+ syntax_head(foo).

:- end_tests(syntax_heads).
