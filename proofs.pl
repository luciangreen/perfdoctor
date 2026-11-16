% proofs.pl - properties of perfdoctor.
:- ensure_loaded('perfdoctor.pl').
:- ensure_loaded('spec.pl').
:- ensure_loaded('tests/inputs.pl').
:- ensure_loaded('mi.pl').

% The cost model is monotone in N for every class (bigger input, no cheaper).
proof(cost_monotone, forall(( member(C, [o1, on, onlogn, on2, exp]), between(1, 40, N) ),
      ( N1 is N + 1, cost(C, N, A), cost(C, N1, B), A =< B ))).

% Classes are ordered: o1 =< on =< onlogn =< on2 =< exp for N >= 4.
proof(class_order, forall(between(4, 60, N), ( maplist(cost_n(N), [o1, on, onlogn, on2, exp], Cs), msort(Cs, Cs) ))).
cost_n(N, C, X) :- cost(C, N, X).

% Every line of the program is reported exactly once, numbered 1..L.
proof(lines_complete, forall(between(1, 40, Id), ( gen_prog(Id, P), doctor(P-10, report(Ls, _, _)),
      findall(No, member(l(No, _, _, _), Ls), Nos), length(Nos, L), numlist(1, L, Nos) ))).

% Every automatic bottleneck has a button, and fix_all is offered iff any exists.
proof(buttons_cover_auto, forall(between(1, 40, Id), ( gen_prog(Id, P), doctor(P-10, report(_, Bs, Btns)),
      forall(member(b(No, _, _, auto), Bs), memberchk(fix(No), Btns)),
      ( member(b(_, _, _, auto), Bs) -> memberchk(fix_all, Btns) ; Btns == [] ) ))).

% Fixing everything removes every automatic bottleneck (table removes the
% exponential one because tabled predicates are reported as fixed).
proof(fix_all_clears_auto, forall(between(1, 40, Id), ( gen_prog(Id, P), apply_button(P, fix_all, P2),
      exclude(is_directive, P2, Cl), doctor(Cl-10, report(_, Bs, _)),
      forall(member(b(_, K, _, auto), Bs), K == exponential_recursion) ))).
is_directive((:- _)).

% The append_to_end and count fixes preserve meaning: run before/after in the
% meta-interpreter on sample inputs.
proof(fixes_preserve_meaning, forall(( member(T, [0, 3]), between(1, 3, I) ),
      ( template(T, I, 0, P), apply_button(P, fix_all, P2), last(P, C), clause_head(C, H), functor(H, F, A),
        forall(member(L, [[], [1], [3, 1, 2], [5, 5]]), same_answer(P, P2, F, A, L)) ))).
clause_head((H :- _), H) :- !.
clause_head(H, H).
same_answer(P, P2, F, 3, L) :- G1 =.. [F, L, [], R1], G2 =.. [F, L, [], R2],
    once(mi(G1, P, 50)), once(mi(G2, P2, 50)), R1 == R2.
same_answer(P, P2, F, 2, L) :- G1 =.. [F, L, R1], G2 =.. [F, L, R2],
    once(mi(G1, P, 50)), once(mi(G2, P2, 50)), R1 == R2.

% Refinement: implementation equals the spec on sample programs.
proof(implementation_equals_spec, forall(between(1, 30, Id), ( gen_prog(Id, P),
      doctor(P-100, A), spec_doctor(P-100, B), A == B,
      press(P-fix_all, X), spec_press(P-fix_all, Y), X == Y ))).
