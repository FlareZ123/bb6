# Raw11 extra parent 137: exact unary-growth leaf

Parent `1RB1RD_1RC0RC_0LA---_1LA1LD_------_------` has a 10,629-node retained search tree, candidate weighted bound 180, and one unresolved leaf before this investigation:

```
1RB1RD_1RC0RC_0LA0RE_1LA1LD_0RD0RF_---1LC
```

The undefined transition is F0. For the partial machine in the centered infinite-stream semantics, let S(n) be A scanning zero just to the left of exactly 2n+4 consecutive ones, with zero padding on both sides. Then:

- Blank reaches S(0) in 10 primitive transitions.
- For every n, S(n) reaches S(n+3) in exactly 8n+34 ordinary transitions.
- Each run is defined, so no completion at F0 can change the infinite orbit.

Proof decomposition: enter C1 in 8 steps, with left half 11(01) followed by zeros and 2n ones on the right; repeat a six-step pair transfer n times; execute an 18-step right turn; sweep left over 2n+2 ones in D1; finish in six steps, returning with six extra ones. The return at index k is at primitive time 12k²+22k+10 with 6k+4 ones. These clocks are unbounded.

[Raw11Extra137.lean](Raw11Extra137.lean) proves the exact seed, unrestricted pair/sweep/turn rules, advance and never. Local Lean 4.36.0-rc2 compiled this file against the exact used centered definitions from Root56.lean (a local dependency slice); advance and never reported only propext and Quot.sound. No sorry or native_decide. [Raw11Extra137Coverage.lean](Raw11Extra137Coverage.lean) ports the standard Root56Coverage bridge to this exact table. It compiled locally against a faithful dependency slice with exact Frontier and weighted definitions and Root56Coverage centering lemmas; never_compatible and weighted report only standard axioms. The transitive original repository dependency closure is **not yet checked**, and no enclosing parent Cover is claimed.

The existing candidate tree (Agent47's retained search, reproduced here) has 6091 side, 1499 coarse pair, 2560 last-hole, 443 split, 35 FAR, one symbolic leaf. The next step is to consume this exact recurrence at that leaf using the existing parent generator and proof-family workflow. Preserve all other branches and the entire unmatched Raw11 roster. This is an intermediate source-level result, not a global upper bound.
