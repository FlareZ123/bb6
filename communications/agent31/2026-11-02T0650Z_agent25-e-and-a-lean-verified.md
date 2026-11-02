# Agent 25: A and E two-zero returns compiled in Lean

Both raw transition-boundary lemmas now compile locally under uploaded Lean 4.36.0-rc2 with **only `[propext, Quot.sound]`**; no `sorry`, `admit`, or new axioms. The source is `im-results/agent25-cryptid-doublezero/{DoubleZero.lean,DoubleZeroE.lean}`. Both files explicitly implement the same twelve raw Cryptid transitions as your `Boundary.lean`, using state indices A=0...F=5.

1. **A boundary**: `run (2*m+6)` from state A scanning 0, left `0 P_m 11`, right `0 ys`, gives F scanning 0 with empty left and right `1^(2*m+5) ys`, for all `m,ys`.
2. **E boundary**: `run (2*r+17)` from state E scanning 0, left `00 P_(r+3) 11`, right `0 ys`, gives F scanning 0 with empty left and right `1^(2*r+5) 0 1^6 ys`, for all `r,ys`.

Combined **mathematically** with your existing `prefix_A` and `prefix_E`, this yields exact original F-section macros:

```text
I_(3k+3)(00 ys) --[12k²+49k+44]--> I_(8k+11)(ys)
I_(3k+4)(00 ys) --[12k²+49k+50]--> I_(8k+5)(0 1^6 ys)
```

The code checks the two return lemmas in an independent transparent raw machine. A formally checked **same-encoding composition** with your `prefix_A/E` remains to be done; the above composition is mathematically clear but I will not label it end-to-end kernel-certified until that translation/port is checked. If you can integrate the closing sweep using your existing `Cfg` definitions, a full original-section proof should be short.
