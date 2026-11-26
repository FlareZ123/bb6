# Raw67 exact weighted maximum 808

The five-hole parent `1RB---_1RC1LB_0RD---_1LD1RE_---0LB_------` has exact weighted maximum **808** under the project's WeightedBound convention. The bound is sharp over all 25^5 = 9,765,625 physical completions.

Attaining completion: `1RB0RC_1RC1LB_0RD0RF_1LD1RE_HHH0LB_1RA0LD`. It executes 807 ordinary moves before querying the undefined E0 transition, and has delay zero.

The regenerated partition has 1514 split nodes including the root, 25738 side-cycle leaves, 6626 immediate last-hole leaves and 2459 open leaves: 2380 FAR, 64 one-block, 11 two-block, two long-epoch and two recursive growth certificates. The open list SHA-256 is `c0115b5f7be2e79b46299a796df771aec2549b3e04fa9cf8cdc690cc48773592`. All source witnesses and the 24 child audits compiled locally using Lean 4.36.0-rc2 and the dependency-closed original source export pinned by [Raw106](2026-11-26-raw106-parent-exact-agent10.md), without mocked imports. Regeneration used the same exact enumerator, pinned spec, symbolic witness algorithm, and 96-leaf proof chunks as Raw79. The old README's split count 1515 was one too large; the regenerated tree contains 1514 including the root. This does not affect the checked partition.

The exported source [Raw67Attainment.lean](../im-results/agent10-tnf-multipump/Raw67Attainment.lean) and [Raw67ParentCover.lean](../im-results/agent10-tnf-multipump/Raw67ParentCover.lean) prove the literal table equality, attaining compatibility, exact halt time and delay, parent Cover, and exact weighted threshold for arbitrary B. All seven axiom profiles are subsets of [propext, Classical.choice, Quot.sound].

This is a complete local parent proof, not a canonical roster removal. Exact canonical membership and consumer integration remain separate.
