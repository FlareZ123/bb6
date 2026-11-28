# F197 epoch conversion: exact 36-reset cycle

Use nearest-first A=10, T=1100, P=AAT, W=AAATAATATAAATTAAAT, R=AATAAAT. For every natural n and arbitrary physical tail X starting in 1,

    B(P^n W R^4 X,e) -> B(P^(n+18) W X,e)

in exactly 2448*n + 26828 primitive live transitions, by a composition of 36 mixed-token reset runs. Iterating gives, for every k,

    B(P^n W R^(4k) X,e) -> B(P^(n+18k) W X,e)

with cost sum_{j=0}^{k-1}(2448*(n+18*j)+26828), i.e. k*(2448*n+26828)+22032*k*(k-1). This is a universal finite-time transfer family, not an assertion that the actual blank orbit visits it infinitely often.

## Proof method

PrefixP.lean proves that an arbitrary leading P counter commutes through every mixed-token return, adding exactly 68*n to the primitive cost. CycleCert.lean proves a general certificate checker for any finite sequence of mixed-token prefix rewrites that accumulates leading P blocks. It checks both finite word equations per row, then lifts to arbitrary n and arbitrary aligned physical continuation, composing exact literal source runs. EpochCycle.lean supplies the 36 instruction schedule, uses ordinary kernel decide (not native_decide) to verify the finite word identities, and proves the arbitrary repetition theorem cycle_many by induction.

The three new modules passed local Lean 4.36.0-rc2 against the exact literal Macro source slice, with propext and Quot.sound only. Full repository import CI for these modules is requested separately.

## Empirical discovery and remaining mathematical obstacle

In accelerated sample exploration, major PPJ descents at reset indices 1567,2173,3552,6656,13586,29243,64524 have leading P counts 114,258,610,1371,3116,7043,15842. They create repeated K=TATAAT blocks, which a global mixed sweep converts to repeated R (with boundary-dependent prefix/suffix). The new 36-return cycle explains the roughly 9/4 leading-counter multiplier after such a descent. The suffix beyond the repetitive bulk changes at every epoch; it is not permissible to declare it inert or infer an infinite lasso from those finite data. The next proof obligation is exact entrance/exit reductions and an inductive tail language or complete recurrence for the changed finite buffer. No Cover or global roster reduction follows yet.

A separate exact crossing-sequence experiment collected 1794 validated tile types from 5000 primitive reset runs (13,307,332 transitions), with a 1736-state finite relation. Its domain DFA had 5407 states and its range DFA 680. Neither range inclusion nor backward safety closure was established; successive forward images still include uncovered configurations, and backward determinization exceeded the cap. N-gram saturation and exact-right pushdown CEGAR also failed to close; do not treat these failed finite searches as proofs of halt/nonhalt.
