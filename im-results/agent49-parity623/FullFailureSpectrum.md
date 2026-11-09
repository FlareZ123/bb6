# Sharp complete fatal first-counter spectra of the original #623 ternary drain

**Agent 49, 9 November 2026. Intermediate mathematical result.** For the exact six-state Cryptids machine `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`, let `B(a,b,d)` be the full source-connected `drainB` accelerator. For every fixed block count `b`, we determine **all** first counters `a` for which the drain fails, without imposing any bound on `a` or `b`. We also give a sharp exponential bound on how many such counters can exist and an explicit family attaining equality. This classifies a component of the accelerated dynamics; reachability from the authentic blank root `D(0,7)` remains open, as does BB(6).

## Exact failure sets and source theorem

Define `E_b = { a ∈ ℕ : B(a,b,d)=none }`. This set is independent of `d` and satisfies the complete recurrences

```text
E_0       = {}
E_(3q)    = {x-1 : x in E_(q-1), x>0}                  (q>0)
E_(3q+1)  = {0} union {x+1 : x in E_q}
E_(3q+2)  = ({0} if 0 in E_q else {}) union {x+1 : x in E_(q+1)}
```

The six source-verified one-level equations in [FlatDrainSource.lean](FlatDrainSource.lean) imply these recurrences for the **entire Option-valued drain**, including failures. Every descendant block count is smaller than its parent. The source-imported Lean module [FullFailureSpectrumSource.lean](FullFailureSpectrumSource.lean) proves `drain_none_iff_badAll`, `drain_none_iff_failure_spectrum`, and `drain_failure_independent_d` for all natural arguments. It also proves all failures lie below `b`, making its first exact finite enumerator exhaustive. The unchanged original-source manual [CI 42600987665](https://github.com/FlareZ123/bb6/actions/runs/42600987665) **succeeded**, auditing these proofs with only `[propext, Quot.sound]`.

## Fast exact finite enumeration

[FastFailureSpectrumSource.lean](FastFailureSpectrumSource.lean) defines `fastSpectrum b` directly by the displayed set recurrences, replacing an `O(b)` scan of possible first counters by one shrinking recursive list and, in the `3q+2` case, one independently evaluated predicate `badAll 0 q`. Its theorem `drain_none_iff_fastSpectrum` establishes exact membership in the **original** drain's failure set for all `a,b,d`.

The block parameter in each recursion shrinks to at most `floor(b/2)`. The list is strictly ordered with no duplicates, proven inductively by the disjointness of the leading zero and the shifted positive list. Generating the complete set requires `O((log b)^2)` elementary arithmetic operations if each auxiliary Boolean test is recomputed; checking a single `a` by `badAll` takes `O(log b)` reductions. Integer bit complexity depends on operand sizes. [SharpSpectrumCapacitySource.lean](SharpSpectrumCapacitySource.lean) also formalizes the no-duplicate claim as `spectrum_nodup`.

## Sharp exponential fatal-spectrum capacity

Let `L(b) = |E_b| = (fastSpectrum b).length`. The new theorem, for every `b≥0`, is

```text
3^L(b) ≤ 2*b + 1.
```

Equivalently, `L(b) ≤ floor(log_3(2*b+1))` (interpreting the logarithm as the largest integral exponent). The bound is **sharp for every cardinality**. Define `u_0=0`, `u_(n+1)=3*u_n+1`, so that `u_n=(3^n-1)/2`. Then, for all `n≥0`,

```text
E_(u_n) = {0,1,...,n-1},     |E_(u_n)| = n.
If |E_b| ≥ n, then b ≥ u_n.
```

Therefore `(3^n-1)/2` is the **exact minimum block count admitting n distinct fatal first-counter values**, simultaneously attained by the first n counters.

The induction in [SharpSpectrumCapacitySource.lean](SharpSpectrumCapacitySource.lean) uses a stronger auxiliary saturation invariant: whenever `3^L(b)=2b+1`, the *preceding* spectrum `E_(b-1)` is empty. For `3q`, cardinality cannot increase and strict capacity follows. For `3q+1`, cardinality increases by exactly one and the induction inequality becomes equality only when the child saturates, preserving the preceding-empty property. For `3q+2`, cardinality may increase by one only if `0∈E_q`; child saturation would force `E_q=∅`, contradiction. Since powers of three are odd, this excludes the one remaining tight integer case and gives strict capacity. The finite induction closes without heuristics. The extremal family follows from repeatedly applying the `3q+1` recurrence.

The exact Lean names are `cap_and_saturation`, `minimum_blocks_for_n_failures`, `boundary_spectrum`, `boundary_power`, `boundary_is_sharp`, and `spectrum_nodup`. All compiled against the source-shaped arithmetic interface with Lean 4.36.0-rc2 and only standard axioms; a targeted original-source CI [workflow](../../.github/workflows/agent49-623-full-failure-spectrum.yml) checks the unmodified upstream source and the full imported proof chain. **Until that expanded CI run succeeds, distinguish these new original-importing modules from the already source-certified FullFailureSpectrumSource.lean.**

Illustrative exact spectra:

```text
b=0:   {}          b=2:   {1}
b=4:   {0,1}       b=5:   {0,2}
b=13:  {0,1,2}     b=14:  {0,1,3}
b=40:  {0,1,2,3}   b=104: {0}
b=121: {0,1,2,3,4}
```

## Research frontier and evidence boundary

The original source is pinned to [google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b). Its full high-level `highLevelNext` may first call `evalA` before `drainB`. Knowing the exact fatal drain spectra classifies that component, but supplies no all-time root history invariant. The physically blank machine is halting-equivalent to the accelerated map from `D(0,7)`; one must still prove that genuine reached inputs avoid every fatal drain spectrum (or exhibit a genuine reachable fatal state). Finite scans and the exact fatal lists do not settle this universal reachability question.

The present findings remain in `im-results/`. No machine-decision theorem, maximal six-state runtime, universal BB(6) upper bound, or publishable BB(6) completion has been established. The next high-value action is to integrate the compact fatal families into an exact root-sensitive predecessor restriction, rather than continuing broad synthetic input enumeration.
