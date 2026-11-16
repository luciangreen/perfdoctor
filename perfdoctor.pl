% perfdoctor - Prolog Performance Doctor.
% Graphs the likely speed of each line of code (every clause head and every
% body goal is a line), identifies bottlenecks, suggests workarounds and
% applies them with buttons: fix(Line) for one, fix_all for all.
%
% Cost model for input size N (estimated inferences for that line in total):
%   o1     constant goals                      1   (N if in a list recursion)
%   on     a pass over the list                N   (N*N if in a list recursion)
%   onlogn sorting                             N*log2(N)
%   on2    a pass inside a recursion           N*N  -> bottleneck
%   exp    two recursive calls on N-1, N-2     2^N  -> bottleneck
% measure/3 gives real measured inferences in SWI-Prolog.
%
% Try:  ?- example(P), doctor_show(P, 100).
%       ?- example(P), press(P-fix_all, P2), forall(member(C, P2), portray_clause(C)).

% ---- entry points used by the tests ----------------------------------------
% doctor(+Prog-N, -report(Lines, Bottlenecks, Buttons))
doctor(Prog-N, report(Lines, Bs, Buttons)) :-
    lines(Prog, Ls),
    findall(l(No, Text, Class, Cost), ( member(line(No, K, G), Ls), line_class(Prog, K, G, Class),
                                         cost(Class, N, Cost), line_text(G, Text) ), Lines),
    findall(b(No, Kind, Advice, How), ( member(line(No, K, G), Ls), bottleneck(Prog, K, G, Kind, Advice, How) ), Bs),
    findall(fix(No), member(b(No, _, _, auto), Bs), Fs),
    ( Fs == [] -> Buttons = [] ; append(Fs, [fix_all], Buttons) ).

% press(+Prog-Button, -NewProg): the new program with readable variable names.
press(Prog-Button, Out) :- apply_button(Prog, Button, P2), maplist(named_clause, P2, Out).

named_clause(C, C2) :- copy_term(C, C2), name_vars(C2, 0, _).

% ---- lines ------------------------------------------------------------------
% line(No, ClauseIndex, head(H) | goal(G))
lines(Prog, Ls) :- clause_lines(Prog, 1, 1, Ls).

clause_lines([], _, _, []).
clause_lines([C|Cs], K, No, [line(No, K, head(H))|Ls]) :-
    parts(C, H, B), body_list(B, Gs), No1 is No + 1,
    goal_lines(Gs, K, No1, No2, Ls, Rest),
    K1 is K + 1, clause_lines(Cs, K1, No2, Rest).

goal_lines([], _, No, No, L, L).
goal_lines([G|Gs], K, No, NoE, [line(No, K, goal(G))|L], R) :-
    No1 is No + 1, goal_lines(Gs, K, No1, NoE, L, R).

parts((H :- B), H, B) :- !.
parts(H, H, true).
body_list(B, []) :- B == true, !.
body_list((A, B), L) :- !, body_list(A, LA), body_list(B, LB), append(LA, LB, L).
body_list(G, [G]).

line_text(head(H), head(F/A)) :- functor(H, F, A).
line_text(goal(G), goal(F/A)) :- functor(G, F, A).

% ---- classification ---------------------------------------------------------
recursive(Prog, K) :- nth1(K, Prog, C), parts(C, H, B), functor(H, F, A),
    body_list(B, Gs), member(G, Gs), functor(G, F, A), !.

self_calls(Prog, K, N) :- nth1(K, Prog, C), parts(C, H, B), functor(H, F, A), body_list(B, Gs),
    findall(x, ( member(G, Gs), functor(G, F, A) ), Xs), length(Xs, N).

base_class(head(_), o1).
base_class(goal(G), C) :- functor(G, F, A), goal_class(F/A, C).

goal_class(F/A, on) :- memberchk(F/A, [append/3, length/2, member/2, memberchk/2, nth0/3, nth1/3,
    last/2, reverse/2, sum_list/2, max_list/2, findall/3]), !.
goal_class(F/A, onlogn) :- memberchk(F/A, [msort/2, sort/2, sort/4, predsort/3]), !.
goal_class(_, o1).

line_class(Prog, K, G, Class) :-
    base_class(G, B),
    (   G = goal(Gl), nth1(K, Prog, C), parts(C, H, _), functor(H, F, A), functor(Gl, F, A),
        self_calls(Prog, K, S), S >= 2
    ->  Class = exp
    ;   recursive(Prog, K), G = goal(Gl), \+ self_goal(Prog, K, Gl)
    ->  bump(B, Class)
    ;   Class = B
    ).

self_goal(Prog, K, G) :- nth1(K, Prog, C), parts(C, H, _), functor(H, F, A), functor(G, F, A).

bump(o1, o1).
bump(on, on2).
bump(onlogn, on2).

cost(o1, _, 1).
cost(on, N, N).
cost(onlogn, N, C) :- log2i(N, L), C is N * L.
cost(on2, N, C) :- C is N * N.
cost(exp, N, C) :- M is min(N, 62), C is 1 << M.

log2i(N, 1) :- N =< 2, !.
log2i(N, L) :- N2 is (N + 1) // 2, log2i(N2, L0), L is L0 + 1.

% ---- bottlenecks and advice -------------------------------------------------
bottleneck(Prog, K, goal(G), exponential_recursion, 'add :- table F/A (memoise) so each subproblem is solved once', auto) :-
    line_class(Prog, K, goal(G), exp), first_self_call(Prog, K, G).
bottleneck(Prog, K, goal(G), append_to_end, 'build the list backwards with [X|Acc] and reverse once at the end', auto) :-
    recursive(Prog, K), nonvar(G), G = append(_, L, _), nonvar(L), L = [_|T], T == [],
    acc_pattern(Prog, K, _).
bottleneck(Prog, K, goal(G), Kind, Advice, manual) :-
    recursive(Prog, K), nonvar(G), functor(G, F, A), \+ self_goal(Prog, K, G),
    \+ ( G = append(_, L, _), nonvar(L), L = [_|T], T == [], acc_pattern(Prog, K, _) ),
    manual(F/A, Kind, Advice).
bottleneck(Prog, K, goal(G), count_with_findall, 'use aggregate_all(count, Goal, N) instead of findall + length', auto) :-
    nonvar(G), G = findall(_, _, L), next_goal(Prog, K, G, G2), nonvar(G2), G2 = length(L2, _), L2 == L.

manual(append/3, append_in_recursion, 'pass a difference list instead of appending each step').
manual(length/2, length_in_recursion, 'carry the length as a counter argument').
manual(member/2, member_in_recursion, 'sort once and use ord_memberchk/2, or use an assoc/2 table').
manual(memberchk/2, member_in_recursion, 'sort once and use ord_memberchk/2, or use an assoc/2 table').
manual(nth0/3, indexing_in_recursion, 'walk the list instead of indexing it each step').
manual(nth1/3, indexing_in_recursion, 'walk the list instead of indexing it each step').
manual(last/2, last_in_recursion, 'keep the last element in an argument').
manual(reverse/2, reverse_in_recursion, 'reverse once outside the recursion').
manual(msort/2, sort_in_recursion, 'sort once before the recursion').
manual(sort/2, sort_in_recursion, 'sort once before the recursion').

first_self_call(Prog, K, G) :-
    nth1(K, Prog, C), parts(C, H, B), functor(H, F, A), body_list(B, Gs),
    member(G1, Gs), functor(G1, F, A), !, G1 == G.

next_goal(Prog, K, G, G2) :- nth1(K, Prog, C), parts(C, _, B), body_list(B, Gs),
    append(_, [G1, G2|_], Gs), G1 == G, !.

% acc_pattern(+Prog, +K, -BaseIndex): clause K is p([X|T], Acc0, R) :- ...,
% append(Acc0, [X'], Acc1), ..., p(T, Acc1, R) and there is a base clause p([], A, A).
acc_pattern(Prog, K, BI) :-
    nth1(K, Prog, C), parts(C, H, _), functor(H, F, 3),
    nth1(BI, Prog, Base), Base \= (_ :- _), functor(Base, F, 3),
    arg(1, Base, E), E == [], arg(2, Base, A1), arg(3, Base, A2), A1 == A2, var(A1).

% ---- buttons ----------------------------------------------------------------
% Fixes are located by the original line numbers. Body rewrites keep clause
% positions; table directives are collected and prepended at the end.
apply_button(Prog, fix_all, P) :-
    lines(Prog, Ls),
    findall(No, ( member(line(No, K, goal(G)), Ls), bottleneck(Prog, K, goal(G), _, _, auto) ), Nos),
    apply_fixes(Nos, Prog, Ls, P).
apply_button(Prog, fix(No), P) :- lines(Prog, Ls), apply_fixes([No], Prog, Ls, P).

apply_fixes(Nos, Prog, Ls, P) :-
    foldl(fix_no(Ls), Nos, Prog-[], P1-Dirs), reverse(Dirs, Ds), append(Ds, P1, P).

fix_no(Ls, No, P0-D0, P-D) :-
    (   member(line(No, K, goal(G)), Ls), bottleneck(P0, K, goal(G), Kind, _, auto)
    ->  fix_kind(Kind, P0, K, G, P, D0, D)
    ;   P = P0, D = D0
    ).

fix_kind(exponential_recursion, P0, K, _, P0, D0, D) :-
    nth1(K, P0, C), parts(C, H, _), functor(H, F, A),
    ( memberchk((:- table(F/A)), D0) -> D = D0 ; D = [(:- table(F/A))|D0] ).
fix_kind(append_to_end, P0, K, G, P, D, D) :-
    acc_pattern(P0, K, BI),
    G = append(Acc0, [X], Acc1),
    replace_goal(P0, K, G, Acc1 = [X|Acc0], P1),
    nth1(BI, P1, Base), Base =.. [F, E, A, _],
    NewBase = (B2 :- reverse(A2, R2)), B2 =.. [F, E, A2, R2], A = A,
    replace_nth(BI, P1, NewBase, P).
fix_kind(count_with_findall, P0, K, G, P, D, D) :-
    G = findall(_, Goal, L), next_goal(P0, K, G, length(L2, N)), L2 == L,
    nth1(K, P0, C), parts(C, H, B), body_list(B, Gs),
    replace_pair(Gs, G, aggregate_all(count, Goal, N), Gs2),
    list_conj(Gs2, B2), replace_nth(K, P0, (H :- B2), P).

replace_goal(P0, K, G, New, P) :-
    nth1(K, P0, C), parts(C, H, B), body_list(B, Gs),
    maplist(swap_goal(G, New), Gs, Gs2), list_conj(Gs2, B2), replace_nth(K, P0, (H :- B2), P).
swap_goal(G, New, X, Y) :- ( X == G -> Y = New ; Y = X ).

replace_pair([G1, _|T], G, New, [New|T]) :- G1 == G, !.
replace_pair([X|T], G, New, [X|R]) :- replace_pair(T, G, New, R).

replace_nth(1, [_|T], X, [X|T]) :- !.
replace_nth(N, [H|T], X, [H|R]) :- N1 is N - 1, replace_nth(N1, T, X, R).

list_conj([], true).
list_conj([G], G) :- !.
list_conj([G|Gs], (G, B)) :- list_conj(Gs, B).

name_vars(T, N0, N) :- var(T), !, atom_concat('V', N0, T), N is N0 + 1.
name_vars(T, N0, N) :- compound(T), !, T =.. [_|As], foldl(name_vars, As, N0, N).
name_vars(_, N, N).

% ---- display ----------------------------------------------------------------
doctor_show(Prog, N) :-
    doctor(Prog-N, report(Lines, Bs, Buttons)),
    format("Likely cost per line for input size ~w (bar = digits of cost):~n", [N]),
    forall(member(l(No, Text, Class, Cost), Lines),
           ( atom_length(Cost, D), Len is min(60, D * 3), length(Cs, Len), maplist(=('#'), Cs),
             atom_chars(Bar, Cs), format("~t~w~4| ~w~t~28| ~w~t~36| ~w ~w~n", [No, Text, Class, Bar, Cost]) )),
    ( Bs == [] -> writeln('No bottlenecks.')
    ; writeln('Bottlenecks:'),
      forall(member(b(No, K, A, How), Bs), format("  line ~w: ~w - ~w (~w)~n", [No, K, A, How])) ),
    format("Buttons: ~w~n", [Buttons]).

% measure(+Goal, -Inferences): real measured cost (SWI-Prolog).
measure(Goal, Inf) :-
    statistics(inferences, I0), ( call(Goal) -> true ; true ), statistics(inferences, I1),
    Inf is I1 - I0.

example([
    rev_slow([], A, A),
    (rev_slow([X|T], Acc, R) :- append(Acc, [X], Acc1), rev_slow(T, Acc1, R)),
    fib(0, 0), fib(1, 1),
    (fib(N, F) :- N > 1, A is N - 1, B is N - 2, fib(A, FA), fib(B, FB), F is FA + FB),
    positions([], _, []),
    (positions([H|T], L, [I|Is]) :- nth1(I, L, H), positions(T, L, Is)),
    (count(L, N) :- findall(X, member(X, L), Xs), length(Xs, N))
]).
