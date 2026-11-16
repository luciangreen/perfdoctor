% inputs.pl - 140 doctor reports and 60 button presses on generated programs.
input(Id, doctor, P-N) :- between(1, 140, Id), gen_prog(Id, P), K is Id mod 4, nth0(K, [10, 50, 100, 1000], N).
input(Id, press, P-B) :- between(141, 200, Id), gen_prog(Id, P),
    ( Id mod 2 =:= 0 -> B = fix_all ; L is 2 + Id mod 9, B = fix(L) ).

lcg(S0, S) :- S is (S0 * 1103515245 + 12345) mod 2147483648.
rnd(M, S0, S, X) :- lcg(S0, S), X is (S >> 16) mod M.

gen_prog(Id, P) :- S0 is Id * 3571, rnd(3, S0, S1, N0), N is N0 + 2, gen_preds(N, 1, S1, Ps), append(Ps, P).

gen_preds(0, _, _, []) :- !.
gen_preds(N, I, S0, [P|Ps]) :- rnd(7, S0, S1, K), rnd(10, S1, S2, M), template(K, I, M, P),
    I1 is I + 1, N1 is N - 1, gen_preds(N1, I1, S2, Ps).

name(Base, I, F) :- atomic_list_concat([Base, I], '_', F).

template(0, I, _, [B, (R :- append(Acc, [X], Acc1), R2)]) :-       % slow reverse with accumulator
    name(rev, I, F), B =.. [F, [], A, A], R =.. [F, [X|T], Acc, Out], R2 =.. [F, T, Acc1, Out].
template(1, I, _, [B0, B1, (R :- N > 1, A is N - 1, C is N - 2, R1, R2, F is FA + FB)]) :-   % fib
    name(fib, I, Fn), B0 =.. [Fn, 0, 0], B1 =.. [Fn, 1, 1], R =.. [Fn, N, F],
    R1 =.. [Fn, A, FA], R2 =.. [Fn, C, FB].
template(2, I, M, [B, (R :- G, R2)]) :-                               % loop with a costly goal
    name(loop, I, F), B =.. [F, [], _, []], R =.. [F, [H|T], L, [Y|Ys]], R2 =.. [F, T, L, Ys],
    K is M mod 8,
    nth0(K, [nth1(Y, L, H), (length(L, Y)), (last(L, Y)), msort(L, Y), reverse(L, Y),
             append(L, [H], Y), memberchk(H-Y, L), sort(L, Y)], G).
template(3, I, _, [(R :- findall(X, member(X, L), Xs), length(Xs, N))]) :-   % count
    name(count, I, F), R =.. [F, L, N].
template(4, I, _, [(R :- Y is 2 * X + 1)]) :- name(plain, I, F), R =.. [F, X, Y].
template(5, I, _, [B, (R :- R2, S is S0 + H)]) :-                    % fine recursion
    name(sum, I, F), B =.. [F, [], 0], R =.. [F, [H|T], S], R2 =.. [F, T, S0].
template(6, I, _, [(R :- msort(L, S), findall(X, member(X, S), Xs), length(Xs, N))]) :-
    name(sorted_count, I, F), R =.. [F, L, N].
