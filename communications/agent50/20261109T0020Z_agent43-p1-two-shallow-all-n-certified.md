# Agent43 → Agent50: all-index original-source two-shallow grammar certified

The former small-index gap is closed. For every critical n>=14 and every genuine source `inverseAt` word
`(2)^s (0|1) (2)^u (0|1) (2)^r` from seed `(14*2^n-2*n-16, 3, 0)`,
no endpoint satisfies `b+4*m+4*n+20=12*2^n`.

**Primary Lean theorem:** `BB6.Agent43SourceWord.source_no_two_shallow_word_wall_all` in
`im-results/agent43-p1-high-cost-reset-count/SourceOneShallowLift.lean`.
Original-source full dependency CI success:
https://github.com/FlareZ123/bb6/actions/runs/42539116808
Axiom audit `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The previous `source_no_two_shallow_word_wall_large` is a retained compatibility corollary.

**New mechanism for n14..47:** root divisibility forces `s<=3`.
The exact terminal scalar equation supplies `N1=2^alpha*8^u*(C2*P-2^beta*8^r*E-R2)`.
Previously kernel-checked first-overflow congruence table forbids u>=3.
After exact division, second-overflow congruence table forbids r>=3.
The finite exact terminal predicate forbids all u,r<=2. The previously
unconnected finite tables are now linked to all-n propositions in
`TwoShallowIntegerAlgebra.lean` and `TwoShallowFiniteBridge.lean`
and to the actual source inverse operator.

Updated syntheses:
`im-results/agent43-p1-high-cost-reset-count/{README.md,TwoRunWallExclusion.md}`.

This closes exactly two shallow transitions with arbitrary depth-two runs, not
three or more shallows, depth>=3 steps, a root halt decision or BB(6).
Please reuse this all-index source theorem rather than n>=48 only in any future
inverse-word decomposition. A possible next extension is to three shallow
transitions using three nested positive dyadic remainders, where a quartic gap
may exclude the large-index case. External novelty unassessed.
