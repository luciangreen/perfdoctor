% mi.pl - depth-bounded meta-interpreter for clause lists (no cut).
% mi(+Goal, +Program, +Depth): Program is a list of clauses. Predicates the
% program defines are taken from it; a small set of safe built-ins is called
% directly; anything else fails (an undefined predicate is a wrong guess).

mi(true, _, _) :- !.
mi((A, B), P, D) :- !, mi(A, P, D), mi(B, P, D).
mi((C -> T ; E), P, D) :- !, ( mi(C, P, D) -> mi(T, P, D) ; mi(E, P, D) ).
mi((A ; B), P, D) :- !, ( mi(A, P, D) ; mi(B, P, D) ).
mi((C -> T), P, D) :- !, ( mi(C, P, D) -> mi(T, P, D) ).
mi(\+ G, P, D) :- !, \+ mi(G, P, D).
mi(G, P, D) :-
    functor(G, N, A), functor(H0, N, A),
    (   defines(P, H0)
    ->  D > 0, D1 is D - 1,
        member(C, P), copy_term(C, C2), parts(C2, H, B), H = G,
        mi(B, P, D1)
    ;   safe_builtin(N/A), call(G)
    ).

defines(P, H) :- member(C, P), parts(C, H1, _), \+ H1 \= H, !.

parts((H :- B), H, B) :- !.
parts(H, H, true).

safe_builtin(B) :- memberchk(B, [(is)/2, (=)/2, (<)/2, (>)/2, (=<)/2, (>=)/2, (=:=)/2, (=\=)/2,
    (==)/2, (\==)/2, (\=)/2, member/2, memberchk/2, append/3, length/2, atom/1, number/1,
    integer/1, atom_length/2, atom_chars/2, msort/2, sum_list/2, max_list/2, min_list/2,
    nth0/3, nth1/3, last/2, reverse/2, findall/3, aggregate_all/3, (!)/0]).
