# Exact gap guards at unit cost

Mathematical derivation, Lean candidate (pending compilation). This companion to LagExact gives the source-safe language rather than an arbitrary positive Micro overapproximation.

For a chronological micro word with compulsory initial one, require:

* after each unit step, v >= 2;
* at every selected-bit start, w >= 10 (w even follows from the one-step equation);
* at the final state, w >= 6.

These are necessary and sufficient for the word to represent a complete LegalGap history (equivalently the original OddCone after the existing source-coordinate transport). In particular, demanding w >= 6 at *every* intermediate unit is too strong: the first unit of a gap may leave w=5, with subsequent zero steps restoring the legal terminal bound.

Proof of necessity: a complete gap of cost e starts with one and has e-1 zeros. If the terminal right coordinate is u>=2, its earlier right values are 2^j u>=2. The first one halves the starting left coordinate (at least ten), and subsequent zeros update w to w_new=w_old+v_new−1. The selected start and final bounds are exactly the original gap guards.

Proof of sufficiency: group the chronological word at each one. The current group has a previously complete legal prefix. A one may start a new group only at w>=10, so the prior group already meets the closing condition w>=6. Each zero extends the existing exact dyadic recurrence without changing its origin. All groups have v>=2 at their end, mass is preserved by the unit equations, and the last group closes when w>=6. No bound on total cost is needed.

Thus the exact guard-aware delayed-word search can reconstruct v=quotient−a, w=T−n−i−1−v at every visited prefix and apply these tests, with no separate inverse traversal. A positive unguarded trace at large cost is not itself a source witness. A pruned empty cover remains a sound extinction certificate if its guard predicate is proved against these unit-cost conditions.

This is an algorithmic/source-language refinement, not a new numerical exclusion or an all-index BB(6) decision.
