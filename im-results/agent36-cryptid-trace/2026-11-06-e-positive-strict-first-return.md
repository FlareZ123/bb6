# Strict physical first return for the exceptional E positive-pair/double-zero sector

**Agent 36, 2026-11-06. Classification: intermediate quantified theorem about a synthetic cylinder, original six-state machine source-certified. This does not decide the actual blank-root future, BB(6), or a global bound.** The endpoint theorem was established in the previous incarnation; the new mathematical content is *strict first positive-time physical F/0 return*, even through transient F/0 visits with marked cells to the left.

## Exact input, timing, and output

Machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`, F/1 undefined. Let `I_n(s)` denote F scanning zero, physically all-zero tape to the left, and right tape `1^n s 0^∞`. In the source, `init xs` prepends **two** ones to `xs`, so `init (replicate (3k+2) true ++ tail)` represents `I_(3k+4)(tail)`. Every finite right suffix `y` is allowed, including the empty suffix.

For all integers `k,q,r≥0` and all finite Boolean suffixes `y`, the original six-state machine has exactly the following **first positive physical F/0** return:

```text
I_(3k+4)(0 (10)^(q+1) 110 (10)^r 0 y)
    --[12k² + 49k + 64 + 4q + 4r primitive steps]-->
I_(8k+5)(0 1^(2q+4) 0 1^(2r+6) y).
```

Here a *physical* F/0 return at step `t` means scanned state F on 0 and `left.any id = false`, covering nonempty left-list representations containing explicit blank zeros. The theorem states no such return at any `0 < t < T`; the initial input itself is a physical F/0 section at `t=0`. It also proves exact raw-configuration equality at `t=T`. The final configuration has the left list literally empty. The terminal frozen halt cannot occur on this finite segment because the exact endpoint is an F/0 state of the original deterministic machine.

Fixed `q,r,y`, increasing `k` by 1 shifts the initial unary length by 3, the returned unary length by 8, and the first-return clock by exactly `24k+61`. This is the `m=0` return branch of Agent37's *conjectural arbitrary-suffix first-event quadratic cocycle*, now proved for the displayed language. It does not establish the cocycle for other arbitrary suffixes.

## Source theorem and verified formal dependency chain

- [`EPositiveFirstFour.lean`](EPositiveFirstFour.lean): quantified four-step exclusions `dBridgeNoPhysical` and `cBaseNoPhysical`, essential because some internal F-state visits are physically nonreturning.
- [`EPositiveFirstChain.lean`](EPositiveFirstChain.lean): `aPositiveFirst` composes nine original transition phases, original inductive `scanNoPhysical`, `walkNoPhysical`, `aTenNoPhysical`, `dPairsNoPhysical`, and Agent2's unchanged source `sweepB_firstF`.
- [`EPositiveFirstBoundary.lean`](EPositiveFirstBoundary.lean): `ePositiveBoundaryFirst` composes the leading E-to-A turn, the arbitrary-length scan, and entire A-sector first-return proof with the exact original E endpoint.
- [`EPositiveFirstComplete.lean`](EPositiveFirstComplete.lean): `originalEPositiveNoEarlier` connects the E boundary to the original F/0 unary entry via Agent2's unchanged source `prefixE_positive_noF` and Agent31's exact original source `prefix_E`; `originalEPositiveFirst` combines its strict physical nonreturn theorem with the earlier `full_E_positive_double_zero_clean` raw endpoint equation.
- Earlier source endpoint: [`EPositiveDoubleZero.lean`](EPositiveDoubleZero.lean) and [`EPositiveSimplified.lean`](EPositiveSimplified.lean).

**Source-level certificate:** [GitHub Actions run 42142050371](https://github.com/FlareZ123/bb6/actions/runs/42142050371), manual workflow [`agent36-e-positive-first.yml`](../../.github/workflows/agent36-e-positive-first.yml), commit `59e8cd887770bdd8ee7138b6aa4b0f3bac14fdd3`. The runner reconstructs Agent31's original D source from its SHA-verified archive and compiles all required original-machine modules and the final Lean file in dependency order with Lean 4.36.0-rc2. `#print axioms originalEPositiveNoEarlier` and `#print axioms originalEPositiveFirst` each produced `[propext, Quot.sound]`, with no `sorryAx` or admitted hypotheses. Earlier attempts with syntactic/term-shape errors failed and were repaired; they provide no positive evidence.

## Significance and next discriminating questions

This closes a genuinely unbounded **first-event** slice, beyond the previously proven endpoint-only assertion. The source theorem holds for all `k,q,r` and arbitrary unchanged tails, and does not rely on a finite sweep or simulated sample.

The decisive unresolved task is **blank-origin reachability**: prove that the authentic blank-tape D itinerary encounters this language, or derive a wider forward/backward closed reachable section grammar incorporating E exceptional packets and A-coded returns. A universal all-suffix shift/conjugacy theorem would be an independent stronger result, requiring proof beyond this cylinder. Keep these notes in `im-results/` until external novelty and a machine-level consequence justify promotion.
