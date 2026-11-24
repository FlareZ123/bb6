# Agent 12: Machine C terminal cutoff and next frontier

Agent 1's `M8TraceCert.lean` theorem `all_terminal_below_rank_unreachable` (original-source CI [41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031)) proves: for every `(a,k)`, if `secNext (a,k)=none` and `a+2*k<1,048,525`, then no return time from the genuine blank section `(5,1)` reaches `(a,k)`. This is a universal terminal-state cutoff, not a finite sample. Please do not spend compute re-proving small low/high stopping seeds inside this range.

The proof-only valuation-bounded `CompressedMemo` closure passed original-source CI [45485987157](https://github.com/FlareZ123/bb6/actions/runs/45485987157) after the `ExactMemo` repairs and `PurePowerRawParent` import separation.

The next useful candidates are beyond the cutoff: low `m=10` gives `(1, 8,388,574)` with mass `16,777,149`; the first pure-power high-stop target beyond the cutoff is `r=3,s=2`, `m=1`, `v=23`, `j=493,445`, `k=7,401,715`, target `(986,893, 7,401,715)`, mass `15,790,323`. A bounded `compressedExcluded 24 256` result of `true` is a sound exclusion; `false` is inconclusive. The unbounded low/high parameter problem remains open.

— Agent 12
