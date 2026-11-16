# Prolog Performance Doctor

Graphs the likely speed of each line of code. Every clause head and body goal is a line. Each line gets a complexity class (o1, on, onlogn, on2 or exp) and an estimated cost for input size N. Bottlenecks are identified with advice, and **buttons** apply fixes: `fix(Line)` for one and `fix_all` for all.

- Automatic fixes: exponential double recursion → `:- table`; appending to the end in a recursion → accumulator plus one `reverse`; `findall` + `length` → `aggregate_all(count)`.
- Manual advice: `length`, `member`, `nth1`, `last`, `reverse` or sorting inside a recursion.
- `measure/2` gives real measured inferences in SWI-Prolog.

```
?- example(P), doctor_show(P, 100).
?- example(P), press(P-fix_all, P2).
```

Proved properties: costs are monotone, classes are ordered, every line is reported once, buttons cover every automatic bottleneck, `fix_all` clears them, fixes preserve meaning (checked in a meta-interpreter), and the implementation equals the spec.

## Tests and proofs

```
swipl run_tests.pl        # runs the 200 saved I/O pairs and checks every proof
swipl tests/gen_io.pl     # regenerates tests/io_pairs.pl from spec.pl
```

- `tests/io_pairs.pl` has 200 saved `io(Id, Predicate, Input, ExpectedOutput)` facts.
- The expected outputs come from `spec.pl`, an independent specification written in a different style from the implementation. Because the implementation is checked against a separate oracle, a pass is real evidence and not the program checking itself.
- `proofs.pl` has machine-checked `proof(Name, Goal)` theorems. Each one is checked exhaustively on a bounded domain or over sample inputs, and its comment gives the general (usually inductive) argument.

All files are plain, portable SWI-Prolog, with no packs needed.
