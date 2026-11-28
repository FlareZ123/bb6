# Cost-adaptive P1 forbidden factors: a late-clock logarithmic window

**Status:** proposed Lean original-source theorems [CyclicTraceLocal.lean](CyclicTraceLocal.lean), [AntiShortTraceLocal.lean](AntiShortTraceLocal.lean); proof audit pending. This is a mathematically new strengthening of the `n+3+K+B` global windows, not a P1 or BB(6) halting decision.

For any even `n≥14` and authentic `Trace n m W a`, let
`T=7*2^n`, fix a factor starting index `i`, and define its **residual positive clock mass**

`R=T-(n+i+2)`.

The original `TracePath.mass` identity gives `v_i+w_i=R+1`, so both coordinates `v,w` at any later time are positive and individually at most `R`. The previous global proof only used `v,w≤T`. It is therefore possible to replace `T` **everywhere** in the repeated-factor analysis, including both transient bounds, by the much smaller `R`.

Let `s=2^r*h`, where `h>0` is odd and `h | (2^K-1)` **or** `h | (2^K+1)` for some `K>0`. Choose `A,B≥0` satisfying

- `R < 2^(A+r)` (enough settling to confine the normalized slope);
- `h*(R+K+1) < 2^B` (enough integral halving to kill the mixed determinant).

If `i+s+A+r+K+B≤m`, then the two `A+r+K+B`-bit factors starting at `i` and `i+s` cannot be identical or bitwise complemented. The **same theorem** handles overlapping factors. The cyclic branch uses the primitive-product lattice proof; the negacyclic branch uses backward-divisibility quotient collision, both without coprimality assumptions.

This is stronger than the global bound whenever `R≪T`, without changing the source machine or assuming another gate/guard. The optimal choices satisfy

`A+r=⌊log₂(R)⌋+1`, `B=⌊log₂(h*(R+K+1))⌋+1`

provided `r≤⌊log₂(R)⌋+1`. The forbidden length is thus approximately `2log₂R+K+log₂h+2`, rather than `2n+K+log₂h+O(1)`.

### Concrete numerical illustration (hypothetical long Trace)

For `n=14`, `T=114688`, h=9, r=0, K=3 with `9|(2^3+1)`:

| Residual R | A | B | Exact forbidden length |
|---:|---:|---:|---:|
| 114,600 | 17 | 20 | 40 |
| 1024 | 11 | 14 | 28 |
| 256 | 9 | 12 | 24 |
| 100 | 7 | 10 | 20 |

The strict inequalities are easily checked using exact integer arithmetic. These are not claims that a P1 trace reaches the corresponding late clocks. The point is that **any** source Trace that did must obey much shorter factor exclusions in its tail.

Source: [ReturnTrace.lean](ReturnTrace.lean) for `TracePath.mass`; [CyclicTraceLocal.lean](CyclicTraceLocal.lean) and [AntiShortTraceLocal.lean](AntiShortTraceLocal.lean) for the proposed original-source bridge. Main remaining work: source Lean audit, then determine whether the late-factor restrictions can be combined with intrinsic P1 prefix arithmetic to force an endpoint exclusion, rather than merely prune repeated patterns.
