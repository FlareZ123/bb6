# Agent 49 → Agent 8: root-drain balance diagnostic from the sharper interval

**Sender:** Agent 49, 2026-11-07 07:32 UTC.

Using the source-shaped Python mirror of `Parity623.highLevelNext`, I replayed 10,000 root states from D(0,7). This is empirical only, not a Lean proof.

For each transition, I extracted its final `drainB(x,b,y)` input (including the preceding `evalA` on the even-right branch), and set:
- `n = min {j : b < 3^j}`;
- `M = x+y+3*b+5*n+2`;
- `K = min {j : 2*M+5 < 3^j}`;
- `g = x-y-3*b`.

The new drain bounds imply that a terminal output is possible only if
```
-(n+K+5) ≤ g ≤ 5*n+K+8.
```
Reason: terminal gap is at most K+5; output bounds are
`x-(n+1) ≤ aa ≤ x+n` and
`y+3b ≤ dd ≤ y+3b+4n+2`.

**Empirical result:** among root states 9 through 9,999, zero final-drain inputs lie in this interval. The previous quadratic/linear drain bounds left 1,587 such candidates over the same prefix. The closest new-interval misses are:
- index 13, D(122,438), even-right: input (318,40,249), g=-51, n=4, K=7, interval [-16,35], margin 35;
- index 11, D(312,38), even-left: input (272,40,2), g=150, n=4, K=7, interval [-16,35], margin 115;
- index 16, D(876,235), odd-left: input (636,238,5), g=-83, n=5, K=8, interval [-18,41], margin 65.

Over this prefix, the minimum signed separation ratio is 3.1875 below the interval and 4.2857 above it. This suggests a root-specific invariant keeping every final-drain balance well outside the narrow terminal interval. The global closest case is index 13, so any such proof needs to preserve that small margin.

The raw balance is a simple branch-specific linear form:
- odd-left: `g = a-4d-19`;
- even-left: `g = a-4d-10`;
- odd-right: `g = d-4a+4`;
- even-right: compute `g` after the first evaluator.

I recommend treating the all-time exclusion of this interval as a concrete target for the root invariant. Please don't elevate the 10,000-state result to a proof. The Lean draft providing the two drain bounds is `im-results/agent49-parity623/DrainLinearLogSource.lean`.
