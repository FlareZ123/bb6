# #429: complete C/0 exclusion for the two regular Junc return types

## Strongest source-certified statement

For the **original six-state, two-symbol #429 instruction table**, both
standard regular source Junc return types contain **zero C/0
instruction starts** at any primitive time, uniformly for all valid
natural-number parameters:

| Initial source configuration | Required condition | Exact guard-certified endpoint | Successful primitive steps |
| --- | --- | --- | ---: |
| `junc (u+1) v w` | `w≥2` | `junc u (v+2) (w-2)` | `4v+10` |
| `junc 0 v w` | `w≥3` | `junc (v+3) 0 (w-3)` | `2v+27` |

Here the *guarded* `runSafe` interpreter aborts precisely if a source
instruction would execute C scanning zero. These equalities certify that
**every intermediate instruction** of both complete ordinary return
types is C/0-free, a conclusion that follows neither from endpoint
equality alone nor from checking only a few C/0 event times.

Moreover, theorems `junc_positive_iter_safe` and
`junc_positive_iter_no_czero` give the same conclusion over **N
consecutive complete positive-u returns** whenever `N≤U` and
`2N≤w`, at every time strictly below the exact accumulated cost
`juncPosFullTime N v`.

**Verified original-source status:** Lean 4.36.0-rc2, unchanged repository
dependency chain, manual CI successful without `sorryAx`:

- [PositiveSafe.lean](PositiveSafe.lean): [CI 42528345611](https://github.com/FlareZ123/bb6/actions/runs/42528345611)
- [ZeroRegularSafe.lean](ZeroRegularSafe.lean): [CI 42528720976](https://github.com/FlareZ123/bb6/actions/runs/42528720976)

The original full-tape zipper model is the one audited in the shared
[one-sided-excursion source proof](../agent6-429-one-sided-excursion/BB429JuncHeadExcursion.lean);
there is no unsound finite cutoff. The source proof imports Agent 1's
[guarded semantics](../agent1-429-w4-boundary/W4CZeroSafe.lean)
and lifts successful guarded runs to all-prefix ordinary zipper runs.

## Proof architecture and mathematical leverage

The positive-u case factors a complete source macro into four preparation
steps, an arbitrarily long `A/0,B/1` sweep of `2(v+1)` steps, and an
`A/1,F/1` sweep of `2(v+2)` steps. The zero-u regular case uses
20 preparation steps, a `B/0,C/1` sweep of `2(v+3)` steps, and a final
`B/1` instruction. Each factor has an explicit `runSafe` equality;
the two source inductions derive exact all-parameter certificates.

The source return endpoints and times were already independently
certified without the C/0 guard. The new mathematical information
lies in the exclusion of **all internal C/0 gateways** in these complete
regular transitions. The proof complements Agent 1's
[complete right-one zero-u C/0 census](../agent1-429-w4-boundary/W4CZeroCount.lean)
and [head maximum certificates](../agent1-429-w4-boundary/W4JuncSecondMax.lean).

## Exact remaining obstacle

The original blank-tape machine's halting criterion is **a genuine C/0
with a marked immediate right neighbor**, equivalently a B/001
event; see [Agent 32's physical theorem](../agent32-429-raw-parent/README.md).

These certificates establish a complete source-level no-gateway result
for the stated return types. Further cases require their own analysis:
positive-u with `w=0,1`, and zero-u with `w=0,1,2` (the zero-u
`w=1` branch is partially or fully covered by Agent 1's separate
right-one census). Most importantly, a source-to-physical theorem
must establish that the **authentic blank-root trajectory** enters
only certified chart/exception branches and that their physical
head history precludes any fatal C/0 event. This all-time
root-sensitive invariant is currently open. The present results
do not determine the halting behavior of #429 from blank, or BB(6).

The proved statements remain in `im-results/` pending evidence of
external mathematical novelty and an authentic-root consequence.
