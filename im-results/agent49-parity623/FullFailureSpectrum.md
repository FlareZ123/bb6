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

The exact Lean names are `cap_and_saturation`, `minimum_blocks_for_n_failures`, `boundary_spectrum`, `boundary_power`, `boundary_is_sharp`, and `spectrum_nodup`. All the complete spectrum, logarithmic list, sharp cardinality, no-duplicates, and full left-sector theorems have passed against the unmodified original Cryptids source in manual source-pinned [CI 42605972987](https://github.com/FlareZ123/bb6/actions/runs/42605972987), with only standard foundational axioms. The new tight-threshold list theorem was subsequently appended and compiled locally with Lean 4.36.0-rc2; its expanded source-pinned run [42606784956](https://github.com/FlareZ123/bb6/actions/runs/42606784956) passed.

Illustrative exact spectra:

```text
b=0:   {}          b=2:   {1}
b=4:   {0,1}       b=5:   {0,2}
b=13:  {0,1,2}     b=14:  {0,1,3}
b=40:  {0,1,2,3}   b=104: {0}
b=121: {0,1,2,3,4}
```

## Exact spectrum at the first-failure threshold and parity refinement

Set `t_a=(3^a+1)/2=boundary(a)+1`. For every initial first counter `a≥1`, the new theorem `tight_spectrum` proves the full failure set at the **first block input causing failure**:

```text
E_(t_a) = {0,1,...,a-2} union {a}.
E_(t_0) = {0}.
```

The single counter `a-1` is absent at that threshold. For example, `t_4=41` gives `E_41={0,1,2,4}` and `t_5=122` gives `E_122={0,1,2,3,5}`. The proof couples the already source-certified `E_(boundary n)=[0,n)` with the `3q+2` recurrence and induction. It is encoded in [SharpSpectrumCapacitySource.lean](SharpSpectrumCapacitySource.lean).

This yields the **parity-resolved sharp minimal block counts**. The least positive `b` with at least `n≥1` distinct **even** fatal first counters is

```text
b_even(n) = (3^(2n-2)+1)/2,
```

and the least block count with at least `n` distinct **odd** fatal first counters is

```text
b_odd(n) = (3^(2n-1)+1)/2.
```

For minimality, the largest among `n` distinct even (respectively odd) natural counters is at least `2n-2` (respectively `2n-1`). The original source-proved `drainB_safe_ones` shows failure at counter `a` requires `b≥t_a`; monotonicity of the exact powers of three gives the claimed lower bounds. The `tight_spectrum` family attains both: it includes every even counter below `2n-2` and the last even counter, or every odd counter below `2n-1` and that last odd counter. The parity-resolved minimality uses this elementary cardinality argument as a paper corollary; `tight_spectrum` itself is the added Lean theorem. No claim of an independent Lean cardinality theorem for that paper corollary is made.

## Original high-level one-step left-sector geometry

The original source [ExactLeftSectorSource.lean](ExactLeftSectorSource.lean), verified in [CI 42605972987](https://github.com/FlareZ123/bb6/actions/runs/42605972987), establishes all-argument exact equivalences:

```text
d odd,  a>=d+5:  highLevelNext(D(a,d))=none iff a-d-5 in E_(d+3)
d even, a>=d+3:  highLevelNext(D(a,d))=none iff a-d-2 in E_(d+2)
```

Consequently for any **fixed** third counter `d`, the entire infinite far-left first-counter ray has a finite, fully explicit list of fatal positions. In even-`d` sectors the candidate `x=0` is discarded because `a=d+2` lies outside that far-left branch and is handled separately by the source's diagonal rule. The exact source theorem `odd_left_none_iff_list` and `even_left_none_iff_list` preserve the appropriate branch boundaries. This is a root-directed classification of the *possible* fatal positions; no blanket root reachability exclusion follows from it.

## Complete odd-third, positive-even-first one-step fatality criterion

[ExactOddSectorSource.lean](ExactOddSectorSource.lean) is checked directly against the original Cryptids `highLevelNext` in [source-pinned CI 42607260924](https://github.com/FlareZ123/bb6/actions/runs/42607260924), without any substitute simulator. For every `a>0` even and `d` odd, the exact theorem `odd_even_none_iff_two_spectra` states

```text
T(D(a,d)) = none  iff
 (a>=d+5 AND a-d-5 in E_(d+3))
 OR
 (a<=d+3 AND d+4-a in E_(a-1)).
```

The derivation explicitly includes the even-first parity guard and the odd-third branch split; these conditions exhaust the positive-even odd-third sector. There is **no remaining call to the intermediate evaluator `evalA`** in this complete one-step halting predicate. The axis `a=0` is universally safe by the prior source theorem `next_zero_total`. Every genuine blank-root survivor has even first counter, so for the odd-third half of the reachable state space, a future halt is equivalent to hitting one of these two explicit sparse, finite-spectrum predicates. This statement is universally quantified over synthetic states and makes **no assertion that the actual orbit ever hits them**.

## Research frontier and evidence boundary

The original source is pinned to [google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b). Its full high-level `highLevelNext` may first call `evalA` before `drainB`. Knowing the exact fatal drain spectra classifies that component, but supplies no all-time root history invariant. The physically blank machine is halting-equivalent to the accelerated map from `D(0,7)`; one must still prove that genuine reached inputs avoid every fatal drain spectrum (or exhibit a genuine reachable fatal state). Finite scans and the exact fatal lists do not settle this universal reachability question.

The present findings remain in `im-results/`. No machine-decision theorem, maximal six-state runtime, universal BB(6) upper bound, or publishable BB(6) completion has been established. The next high-value action is to integrate the compact fatal families into an exact root-sensitive predecessor restriction, rather than continuing broad synthetic input enumeration.
