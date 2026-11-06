# P1: source-exact fixed-reset budgets and exceptional inverse exits

**Research state (6 November 2026): original-source-verified inverse restrictions; P1 blank-start halting and BB(6) remain open.** [Detailed mathematics and verification history](FULL_RESEARCH_LOG.md).

## Source-certified tools

- Exact critical odd inverse words admit reset-count budgets. The original `CountCone` connection and arbitrary-count seed-to-tail theorem passed [CI 41759728110](https://github.com/FlareZ123/bb6/actions/runs/41759728110); the general source bound passed [CI 41760402128](https://github.com/FlareZ123/bb6/actions/runs/41760402128). Fixed-reset corollaries include a five-reset exclusion for `n≥7166`. No uniform maximum reset count is proved.
- The exceptional `c=1` exit has independent source-certified exponential and near-double-logarithmic cost restrictions: [ExceptionalExpSource.lean](ExceptionalExpSource.lean), [CI 41766193226](https://github.com/FlareZ123/bb6/actions/runs/41766193226), and [ExceptionalNearDoubleSource.lean](ExceptionalNearDoubleSource.lean), [CI 41837316502](https://github.com/FlareZ123/bb6/actions/runs/41837316502). These restrict the exception without eliminating it globally.
- Original-source zero-even feeder and first-critical-index descent proofs are in [ZeroEvenRigiditySource.lean](ZeroEvenRigiditySource.lean) and [ZeroEvenDescentSource.lean](ZeroEvenDescentSource.lean), [CI 41905298143](https://github.com/FlareZ123/bb6/actions/runs/41905298143). The broader all-even descent workflow [41966304328](https://github.com/FlareZ123/bb6/actions/runs/41966304328) completed successfully; verify its exact checked revision for theorem reuse. Synthetic even-hub reconstructions are local route descriptions, without proving blank ancestry.

## Missing theorem

There is no exhaustive source-valid exclusion across **all** inverse words, arbitrarily many resets, zero/even-hub alternatives, and exceptional `c=1` exits from the authentic blank root. For a proposed new index, authenticate every inverse-exit branch and the actual root before promotion. Prefer uniform family results over extending a finite sieve.

See the [P1 result map](../../results/README.md), [Agent43 cost bound](../agent43-p1-high-cost-reset-count/README.md) and [full research log](FULL_RESEARCH_LOG.md) for exact recurrence equations, numerical demonstrations, counterexamples and complete provenance.
