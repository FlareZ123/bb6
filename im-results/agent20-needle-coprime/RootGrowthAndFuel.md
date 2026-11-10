# An authentic-root logarithmic drift bound and finite reachability cutoff for Space Needle

**Agent 20, 10 November 2026. Intermediate mathematical result.** This note concerns the **original blank-root orbit** of the pinned [Cryptids Space Needle source](https://github.com/google-deepmind/cryptids/blob/ced8f9f44f67a167d5ecc03e687b048c67926371/BusyBeaver/BB6/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean). It does **not** decide the machine's halting or BB(6).

## The exact quantitative statement

Write the shifted high-level counter `b=d+2`. In every successful source step, its unique odd-part representation is `b=2^v(2q+3)` for natural `v,q`, and the next shifted counter is

```text
b' = b + v + 3(q+1).
```

A uniform, unconditional edge inequality is

```text
b' - b >= floor(log2(b)) + 2.
```

The proof is elementary but source-exact: `2q+3<2^(q+2)`, whence `b<2^(v+q+2)`. If `2^M<=b`, then `M+2<=v+3(q+1)`. The statement is independent of how `b` was prepared and applies to the genuine blank-root updates.

For **every finite prefix** of `n` successful high-level updates starting at the genuine `N 1`, and every `M` such that `2^(M+1)<=n`, the reached counter `d_n` satisfies

```text
floor(n/2) * (M+2) <= d_n+2.
```

Indeed the first `2^M` updates increase the shifted counter to at least `2^M`; each later update increases it by at least `M+2`; the later count is at least `floor(n/2)`. Choosing `M=floor(log2(n))-1` for `n>=2` yields the closed-form root theorem

```text
floor(n/2) * (floor(log2(n))+1) <= d_n+2.
```

This is a finite-prefix theorem and does **not** assume that the trajectory continues indefinitely. If a global infinite successful trajectory exists, its counter divided by its step index diverges. In particular such a root trajectory has natural density zero in the natural counters; the density corollary is a straightforward paper consequence, not a separately compiled Lean statement.

## Exact bounded single-target root decision

For a candidate genuine-root counter `d`, select any natural `M`. If the original blank-start high-level orbit first reaches `d` after `n` successful updates, then either

```text
n < 2^(M+1)
```

or

```text
n <= 2 * floor((d+2)/(M+2)) + 1.
```

Consequently define

```text
timeFuel(d,M) = max(2^(M+1), 2*floor((d+2)/(M+2))+2)
optimizedFuel(d) = timeFuel(d, floor(log2(d+2))/2).
```

**Exact root criterion:** `ReachN d` if and only if the authentic high-level blank-start iterate reaches `N d` at an index `n<optimizedFuel(d)`. For large `d`, this bounds the necessary number of updates by `O(d/log d)`, improving the prior elementary linear cutoff in the size of the target counter. It is still exponential in the binary input length.

A single-pass, source-connected Boolean checker `optimizedScan(d)` follows the original exact high-level transition and stops when the target is encountered or after `optimizedFuel(d)` inspections. Its theorem is

```lean
optimizedScan_spec (d : Nat) : optimizedScan d = true ↔ ReachN d
```

The scan keeps the current state and remaining iteration fuel; it avoids constructing a complete list of all earlier source states. The underlying inverse checker `NeedleRootDecisionSource.reverseCheck` remains useful for sparse inverse graphs; the present forward bound does not by itself establish a faster running time for inverse enumeration.

## Proof artifacts and verification

- [NeedleGrowth.lean](NeedleGrowth.lean): standalone dyadic increment, log-growth, and conditional infinite-orbit theorem. Lean 4.36.0-rc2 local kernel, only `propext` and `Quot.sound`.
- [NeedleGrowthSource.lean](NeedleGrowthSource.lean): direct unchanged source bridge for the pinned high-level `highLevelNext`; **successful [source run 42727978996](https://github.com/FlareZ123/bb6/actions/runs/42727978996)**, only standard axioms.
- [NeedleGrowthFinite.lean](NeedleGrowthFinite.lean): finite-prefix dyadic and closed-form logarithmic bounds, local kernel with no `sorry`.
- [NeedleGrowthRoot.lean](NeedleGrowthRoot.lean): true-root finite iterate bound, dyadic-index restriction, precise cutoff and Boolean specification; initial finite-prefix bridge **source checked in [run 42728646750](https://github.com/FlareZ123/bb6/actions/runs/42728646750)**. The additional optimized-fuel theorem requires a source check after the `CollatzReachesIn` elaboration repair.
- [NeedleGrowthScan.lean](NeedleGrowthScan.lean): exact executable one-pass Boolean checker, locally checked in Lean 4.36 with original-source-shaped declaration interfaces; source import audit is pending.
- [Manual source workflow](../../.github/workflows/agent20-needle-growth.yml) imports the unchanged original upstream source and compiles the files without any `sorry`.

**Status caution:** Lean 4.36 local testing of the source wrappers used declaration-shaped interface stubs for unavailable upstream imports; those are deliberately absent from the committed proof files. The full source CI run is the authoritative check of the genuine machine's theorem. The lower-bound and original finite-run theorems have already passed that source audit. Follow-up source certification for the refined cutoff and executable checker must be checked separately and reported accurately.

## Exact scope and research implications

The theorem speaks about the actual blank-start orbit and all of its finite successful prefixes. This differs from predecessor constructions that establish legal incoming edges for arbitrary synthetic states. It is a quantitative necessary condition on reachable states and a reusable fixed-target decision acceleration. The result provides no contradiction at terminal counters `2^K-2`, whose exponents remain unbounded, and proves no bound on the six-state champion's step count. Source-bound decisions of individual targets are insufficient to settle an unbounded existential over all terminal powers. A decisive advance would require a root-history invariant excluding all remaining terminal feeders, a genuine terminal witness, or another universal certificate.
