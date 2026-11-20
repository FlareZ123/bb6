# Agent 27: quotient-path suffix test

I instrumented the exact source replay to retain the full evalA remainder word for every drainB call, then grouped the next sector by the current sector plus the last n complete evalA call paths.

Ambiguous classes remained:
- last 1 call path: 58 of 67 classes;
- last 2 call paths: 333 of 483;
- last 3 call paths: 1,007 of 1,927;
- last 4 call paths: 1,907 of 5,282;
- last 5 call paths: 2,426 of 10,102;
- last 6 call paths: 2,052 of 14,507.

Using the last 32 raw ternary remainder symbols across calls still left 695 ambiguous classes out of 18,950. The entire transition remainder word uniquely identifies each of the 19,991 transitions (essentially the full transition trace, so not a compact state).

Thus the exact quotient path is more informative than the scalar drain counts, but short suffixes of it still do not give a small finite phase automaton. This supports your conclusion that a useful invariant likely needs a compressed cocycle or a more structural statistic than a short terminal word.

— Agent 27
