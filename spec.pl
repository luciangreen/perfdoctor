% spec.pl - independent oracle for perfdoctor: lines are numbered by prefix
% sums, every line is classified by one decision table, and the buttons are
% re-implemented as clause-index edits.

spec_for(doctor, spec_doctor).
spec_for(press, spec_press).

spec_hb(C, H, B) :- ( C = (H :- B) -> true ; H = C, B = true ).
spec_goals(B, Gs) :- ( B == true -> Gs = [] ; spec_flat(B, Gs) ).
spec_flat(B, L) :- ( nonvar(B), B = (X, Y) -> spec_flat(X, LX), spec_flat(Y, LY), append(LX, LY, L) ; L = [B] ).

% spec_line(+Prog, -No, -K, -Kind): Kind = head(H) or goal(G, Pos).
spec_line(Prog, No, K, Kind) :-
    length(Prog, NC), between(1, NC, K),
    spec_offset(Prog, K, Off), nth1(K, Prog, C), spec_hb(C, H, B), spec_goals(B, Gs),
    (   No = Off, Kind = head(H)
    ;   nth1(P, Gs, G), No is Off + P, Kind = goal(G, P)
    ).

spec_offset(Prog, K, Off) :-
    K1 is K - 1, length(Pre, K1), append(Pre, _, Prog),
    foldl(spec_len, Pre, 1, Off).
spec_len(C, A0, A) :- spec_hb(C, _, B), spec_goals(B, Gs), length(Gs, N), A is A0 + 1 + N.

spec_selfs(Prog, K, S) :-
    nth1(K, Prog, C), spec_hb(C, H, B), spec_goals(B, Gs), functor(H, F, A),
    include(spec_is(F/A), Gs, Ss), length(Ss, S).
spec_is(F/A, G) :- functor(G, F, A).

spec_kind(G, on) :- functor(G, F, A), member(F/A, [append/3, length/2, member/2, memberchk/2, nth0/3,
    nth1/3, last/2, reverse/2, sum_list/2, max_list/2, findall/3]), !.
spec_kind(G, onlogn) :- functor(G, F, A), member(F/A, [msort/2, sort/2, sort/4, predsort/3]), !.
spec_kind(_, o1).

spec_class(_, _, head(_), o1).
spec_class(Prog, K, goal(G, _), Cl) :-
    nth1(K, Prog, C), spec_hb(C, H, _), functor(H, F, A), spec_selfs(Prog, K, S), spec_kind(G, B),
    (   functor(G, F, A), S >= 2 -> Cl = exp
    ;   functor(G, F, A) -> Cl = B
    ;   S >= 1, B == on -> Cl = on2
    ;   S >= 1, B == onlogn -> Cl = on2
    ;   Cl = B ).

spec_cost(o1, _, 1).
spec_cost(on, N, N).
spec_cost(on2, N, C) :- C is N * N.
spec_cost(exp, N, C) :- C is 2 ^ min(N, 62).
spec_cost(onlogn, N, C) :- spec_clog(N, 1, 2, L), C is N * L.
spec_clog(N, L, P, R) :- ( P >= N -> R = L ; L1 is L + 1, P1 is P * 2, spec_clog(N, L1, P1, R) ).

spec_doctor(Prog-N, report(Lines, Bs, Buttons)) :-
    findall(l(No, T, Cl, Cost), ( spec_line(Prog, No, K, Kd), spec_class(Prog, K, Kd, Cl), spec_cost(Cl, N, Cost),
                                  ( Kd = head(H) -> functor(H, F, A), T = head(F/A) ; Kd = goal(G, _), functor(G, F, A), T = goal(F/A) ) ), Lines),
    findall(b(No, Kn, Ad, How), ( spec_line(Prog, No, K, goal(G, P)), spec_bneck(Prog, K, G, P, Kn, Ad, How) ), Bs),
    findall(fix(No), member(b(No, _, _, auto), Bs), Fs),
    ( Fs = [] -> Buttons = [] ; append(Fs, [fix_all], Buttons) ).

spec_bneck(Prog, K, G, P, Kn, Ad, How) :-
    nth1(K, Prog, C), spec_hb(C, H, B), spec_goals(B, Gs), functor(H, F, A), spec_selfs(Prog, K, S),
    findall(b(Kn0, Ad0, How0), (
        (   functor(G, F, A), S >= 2, once(( nth1(P1, Gs, G1), functor(G1, F, A) )), P1 =:= P,
            Kn0 = exponential_recursion, Ad0 = 'add :- table F/A (memoise) so each subproblem is solved once', How0 = auto
        ;   S >= 1, spec_end_append(G), spec_acc(Prog, K, _),
            Kn0 = append_to_end, Ad0 = 'build the list backwards with [X|Acc] and reverse once at the end', How0 = auto
        ;   S >= 1, \+ functor(G, F, A), \+ ( spec_end_append(G), spec_acc(Prog, K, _) ),
            functor(G, GF, GA), spec_manual(GF/GA, Kn0, Ad0), How0 = manual
        ;   nonvar(G), G = findall(_, _, L), P2 is P + 1, nth1(P2, Gs, G2), nonvar(G2), G2 = length(L2, _), L2 == L,
            Kn0 = count_with_findall, Ad0 = 'use aggregate_all(count, Goal, N) instead of findall + length', How0 = auto
        ) ), Found),
    member(b(Kn, Ad, How), Found).

spec_end_append(G) :- nonvar(G), G = append(_, L, _), nonvar(L), L = [_|T], T == [].

spec_acc(Prog, K, BI) :-
    nth1(K, Prog, C), spec_hb(C, H, _), functor(H, F, 3),
    nth1(BI, Prog, Base), \+ Base = (_ :- _), Base =.. [F, E, X, Y], E == [], X == Y, var(X).

spec_manual(append/3, append_in_recursion, 'pass a difference list instead of appending each step').
spec_manual(length/2, length_in_recursion, 'carry the length as a counter argument').
spec_manual(member/2, member_in_recursion, 'sort once and use ord_memberchk/2, or use an assoc/2 table').
spec_manual(memberchk/2, member_in_recursion, 'sort once and use ord_memberchk/2, or use an assoc/2 table').
spec_manual(nth0/3, indexing_in_recursion, 'walk the list instead of indexing it each step').
spec_manual(nth1/3, indexing_in_recursion, 'walk the list instead of indexing it each step').
spec_manual(last/2, last_in_recursion, 'keep the last element in an argument').
spec_manual(reverse/2, reverse_in_recursion, 'reverse once outside the recursion').
spec_manual(msort/2, sort_in_recursion, 'sort once before the recursion').
spec_manual(sort/2, sort_in_recursion, 'sort once before the recursion').

% ---- buttons ----------------------------------------------------------------
spec_press(Prog-Btn, Out) :-
    spec_doctor(Prog-10, report(_, Bs, _)),
    ( Btn == fix_all -> findall(No, member(b(No, _, _, auto), Bs), Nos) ; Btn = fix(No1), Nos = [No1] ),
    spec_apply(Nos, Prog, Prog, [], P1, Ds),
    append(Ds, P1, P2),
    findall(C, ( member(C0, P2), copy_term(C0, C), spec_name(C, 0, _) ), Out0),
    Out = Out0.

% Lines are looked up in the original program; the goal is then found by
% identity in the current version of its clause.
spec_apply([], _, P, Ds, P, Ds).
spec_apply([No|Nos], Orig, P0, D0, P, D) :-
    (   spec_line(Orig, No, K, goal(G, _)),
        nth1(K, P0, C), spec_hb(C, _, B), spec_goals(B, Gs), nth1(Pos, Gs, G1), G1 == G,
        spec_bneck(P0, K, G, Pos, Kn, _, auto)
    ->  spec_fix(Kn, P0, K, G, Pos, P1, D0, D1)
    ;   P1 = P0, D1 = D0 ),
    spec_apply(Nos, Orig, P1, D1, P, D).

spec_fix(exponential_recursion, P, K, _, _, P, D0, D) :-
    nth1(K, P, C), spec_hb(C, H, _), functor(H, F, A),
    ( member(Dir, D0), Dir == (:- table(F/A)) -> D = D0 ; append(D0, [(:- table(F/A))], D) ).
spec_fix(append_to_end, P0, K, G, Pos, P, D, D) :-
    G = append(Acc0, [X], Acc1),
    spec_set_goal(P0, K, Pos, Acc1 = [X|Acc0], P1),
    spec_acc(P1, K, BI), nth1(BI, P1, Base), Base =.. [F, E, _, _],
    NB =.. [F, E, A2, R2], spec_set(BI, P1, (NB :- reverse(A2, R2)), P).
spec_fix(count_with_findall, P0, K, G, Pos, P, D, D) :-
    G = findall(_, Goal, _), nth1(K, P0, C), spec_hb(C, H, B), spec_goals(B, Gs),
    P2 is Pos + 1, nth1(P2, Gs, length(_, N)),
    Pm is Pos - 1, length(Pre, Pm), append(Pre, [_, _|Post], Gs),
    append(Pre, [aggregate_all(count, Goal, N)|Post], Gs2),
    spec_conj(Gs2, B2), spec_set(K, P0, (H :- B2), P).

spec_set_goal(P0, K, Pos, New, P) :-
    nth1(K, P0, C), spec_hb(C, H, B), spec_goals(B, Gs),
    Pm is Pos - 1, length(Pre, Pm), append(Pre, [_|Post], Gs), append(Pre, [New|Post], Gs2),
    spec_conj(Gs2, B2), spec_set(K, P0, (H :- B2), P).

spec_set(I, L, X, R) :- I1 is I - 1, length(Pre, I1), append(Pre, [_|Post], L), append(Pre, [X|Post], R).

spec_conj([G], G) :- !.
spec_conj([G|Gs], (G, B)) :- spec_conj(Gs, B).

spec_name(T, N0, N) :- var(T), !, atom_concat('V', N0, T), N is N0 + 1.
spec_name(T, N0, N) :- compound(T), !, T =.. [_|As], foldl(spec_name, As, N0, N).
spec_name(_, N, N).
