# Canonical58: source-accepted Raw113 delta

**Status:** source-accepted conditional theorem; not a universal upper bound.

The accepted Canonical59 integration (five parent Covers, 59 residual representatives) is strengthened by consuming the distinct Raw113 E1 parent. The resulting Canonical58 roster has 58 retained representatives. Raw59 remains explicitly in the complement.

## Accepted proof

- Base: Canonical59, workflow run [45880290680](https://github.com/FlareZ123/bb6/actions/runs/45880290680), artifact 15147189928.
- Raw113 parent: source-accepted exact weighted maximum 2,674, with parent Cover theorem `BB6.Agent25Raw113.cover113`; see [the Raw113 parent result](2026-11-26-raw113-parent-exact-agent25.md).
- Membership and graft: [`Canonical59Raw113Membership.lean`](../im-results/agent31-shared-core/Canonical59Raw113Membership.lean) proves exact source-table equality, unique membership in Canonical64 and Canonical59, the blank-start root, and the Raw113 Cover lifted to the common weighted floor 6,766,859. [`Canonical58Raw113Graft.lean`](../im-results/agent31-shared-core/Canonical58Raw113Graft.lean) removes Raw113 from the accepted 59-entry roster and proves the 58-entry complement, retained Raw59 membership, parent root and Cover, quotient-soundness composition, and the fixed-score exactness interface.
- CI acceptance: [run 45891227622](https://github.com/FlareZ123/bb6/actions/runs/45891227622), source revision `66cf14dcfba8403f4e2ddc7f7a2d1d85accc90fb). The uploaded `canonical58-raw113-graft-integrated` artifact is ID 15151767938, SHA-256 `b2914335f5bba7b9e410d656d0bcce263738016957af15db814b05442fc5b404`.

The configured axiom gate accepts only `propext`, `Classical.choice`, and `Quot.sound`; the workflow also rejects `sorryAx` and `native_decide` in the consumer log. The exported fixed-score theorem is `BB6.Agent31Canonical58Raw113Graft.exact_at_champion_score`.

## Mathematical statement and limitation

At the exact attained champion score (B = 	exttt{proposedTM63Moves} + 7), the accepted theorem concludes `ExactBB6 B` from Covers for every entry of the 58-element `roster58`. The theorem reuses the already source-certified blank-start champion witness and score inequality. The common floor 6,766,859 is only the parent-Cover reduction threshold; it is not asserted to be the champion score.

This result removes one exact parent from the conditional quotient complement. It does **not** prove the remaining 58 Covers, does not provide a universal upper bound, and does not determine BB(6). The next useful cuts must preserve the complete retained complement; Raw59 is still outstanding.
