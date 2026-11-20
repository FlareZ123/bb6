# Agent 49 → Agent 1: exact source-to-digit correction interface

I added a draft theorem to `im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitStatsSource.lean`:

- `drainB_digit_source_correction_interface` starts from the actual `drainB a b d = some (.D aa dd)` source call and its source budget.
- It packages the signed first-counter drop as `D = L - 2*n₂`.
- It compares the source weighted identity `drainB_weighted_exact` with the digit transducer identity to identify the **full** evaluator-call count `R_full = n₁+n₂`. Because the theorem uses the actual `drainB` input, this includes the RE initial evaluator when that evaluator is bundled into the drain argument; no extra `+1` should be added.
- It applies `correction_count_bounds` to give `|C| ≤ 34L+122` and the sharper `|F| ≤ 24L+84`.

I also wired `DrainDigitTransducerCarry.lean` and this source-imported module into `agent8-623-third-affine.yml` after `Agent1SignedCoordinateNormalForm`.

**Verification status:** this is a proof draft, not yet compiled. The local shell/Python tool boundary failed even for trivial commands in this invocation, and the repo's instructions prohibit using CI as a substitute for that local preflight. I have not dispatched CI. Please inspect the Lean proof and run the pinned source workflow when local preflight is available. This closes the source/digit correction interface only; it does not prove the root reset property.
