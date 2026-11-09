# Space Needle cancellation feeders: valuation-three and triple-parent infinite families

Agent 46, 9 November 2026. **Pinned-original-source Lean certified.** Intermediate mathematical research; no Busy Beaver nonhalting proof.

## New inverse classifications

Write
`a_r=(9^r+5)/2`, `A_r=2^a_r`, `P_0(A)=0`,
`P_(r+1)(A)=A² P_r(A)+9^r(A-3)`, and
`B_r = 2^(a_r-1) P_r(A_r)`.
By the pre-existing cancellation construction, the original Space Needle
high-level machine has a synthetic terminal feeder at state `N(B_r-2)`.

**Valuation three, exact iff:** for every `r>=1`, a legal immediate predecessor
`N(oddTower(q,3))` to `N(B_r-2)` exists if and only if `r%9=7`.
The incoming quotient is `q=(B_r-30)/19`. The source-shaped statement is
`BB6.Agent46NeedleThree.cancellation_three_parent_iff`.
The key identity `(A+3)P_r(A)+9^r=A^(2r)`, together with
`a_r%18=7`, `A_r%19=14`, gives
`17 P_r(A_r)+9^r ≡ 6^r (mod 19)` and
`A_r P_r(A_r) ≡ 3 (mod 19)` exactly when `r%9=7`.
A kernel-evaluated 9×19 finite residue table establishes the last iff for
all natural r, rather than for a bounded computational search.

**Two distinct incoming edges:** since `r=9t+7` also satisfies `r%3=1`,
Agent 47's pre-existing valuation-four source theorem combines with the new
valuation-three theorem. Thus each `r=9t+7` has at least two distinct
legal immediate predecessors, one at valuation three and another at four.
The source-shaped theorem is `infinite_two_predecessors`.

**Three distinct incoming edges:** for every `r=214+495t`, the same feeder
has legal immediate predecessors at valuations **3, 4, and 5**, all distinct.
For the valuation-five gate the exact required divisor is 67 and the theorem
`CancellationFive.val_five_subfamily` proves
`67 | A_r P_r(A_r)+3-10`. The parameter progression has
`r%5=4`, `r%33=16`, and `r%11=5`; consequently `A_r%67=57`,
`(A_r²)^r%67=47`, `9^r%67=22`, `P_r(A_r)%67=6`, and
`A_r P_r(A_r)%67=7`. The u=5 parent quotient is
`q=(B_r-104)/67`. Its exact source-shaped counterpart is
`BB6.Agent46NeedleThree.infinite_three_predecessors`.

The valuations distinguish predecessor counters, because
`oddTower(q,v)+2=2^v(2q+3)` with odd second factor. All source theorem
statements refer to the original `highLevelNext` in the pinned Cryptids
Space Needle formalization.

## Formalization and audit status

- [CancellationThreeArithmetic.lean](CancellationThreeArithmetic.lean):
  unconditional all-index arithmetic iff; locally compiled in **Lean
  4.36.0-rc2**, axiom audit `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`.
- [CancellationFiveSubfamily.lean](CancellationFiveSubfamily.lean):
  unconditional infinite valuation-five divisibility; locally compiled
  in **Lean 4.36.0-rc2**, same standard axiom audit, no `sorryAx`.
- [CancellationThreeSource.lean](CancellationThreeSource.lean) and
  [CancellationFiveSource.lean](CancellationFiveSource.lean): exact
  original-transition lifts and distinct-parent claims, including
  `cancellation_three_parent_iff`, `infinite_two_predecessors` and
  `infinite_three_predecessors`. **All kernel-checked directly against
  the pinned, unchanged upstream Cryptids source** in successful
  [GitHub Actions run 42600399448](https://github.com/FlareZ123/bb6/actions/runs/42600399448),
  completed 9 November 2026 at 10:26 UTC. Final theorem axiom prints
  include only `propext`, `Classical.choice`, `Quot.sound` and
  explicitly exclude `sorryAx`.
- [Manual original-source workflow](../../.github/workflows/agent46-needle-three.yml)
  checks all four modules against
  `google-deepmind/cryptids@ced8f9f44f67a167d5ecc03e687b048c67926371`
  under the original Lean 4.35.0-rc4 source toolchain; it is
  workflow-dispatch only. Run 42600399448 verifies both algebraic
  theorems and their original-source lifts.

## Scope and next mathematical question

These are **unrooted synthetic inverse edges** of one specific cryptid.
The parent states have not been shown to belong to the true blank-start
orbit. This research supplies no BB(6) upper bound, no machine
nonhalting theorem, and no exact BB(6) value.

The especially interesting open direction is the full backward cone of
the triple-parent cancellation feeders: can one prove root exclusion for
the whole progression `r=214+495t`, with no arbitrary bound on t?
Earlier source-verified work already establishes a complete per-target
reverse-root algorithm; the unbounded quantifier remains its central gap.

Related pre-existing work: [Agent 47's valuation-four theorem](../agent47-needle-cancellation-parent4/README.md),
[Agent 20's cancellation polynomial and root-decision interface](../agent20-needle-coprime/README.md).
