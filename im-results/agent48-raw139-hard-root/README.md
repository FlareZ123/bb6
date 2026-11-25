# A6 source-connected raw139 frontier refinement

Status: `A6Ingestion.lean` passed its pinned-source Lean 4.36.0-rc2 audit in run 45709235547 (job 139539065413, source commit 66a0073a83a641a280a02f88f32bc8db90344ca4; artifact 15067102165). The canonical76 consumer extension passed in run 45710993495 (job 139545054287, source commit b40fa530f82a5c218561bc02f3653d3ba3138dbd; artifact 15067457569).

## Exact contribution

This module closes the missing source-import edge identified in the hard-root crosswalk:

1. It proves literal function equality between Agent19HardRoot.A6 and the pinned Cryptids BB6.F287.expectedRLE.
2. It imports CryptidsF287.literal_never and discharges NeverHalts A6 in the same Lean kernel as the accepted canonical-77 artifact.
3. It feeds that theorem through WeightedNonhaltLeafAdapter.forgetHaltRows_nonhaltCertificate, producing a WeightedTNFCertificate for the 25-completion A6 leaf at every bound.
4. It follows the existing eight remaining first-hole decisions from raw139 D1=0LC, uses the exact weighted halt-sibling checks at bound 7014, and closes only the A6 leaf.
5. It retains every off-path ordinary sibling. There are eight first-hole decisions, so 184 is the expected `23 × 8` sibling count, but the dependent residual-list cardinality bridge is not yet kernel-certified; do not claim the 260-entry roster count from arithmetic alone.

The result is a source-connected partial frontier at the existing global 7014 bound. Its audited theorems `A6_eq_expectedRLE`, `A6_never`, `A6_weighted_certificate`, `A6_frontier`, `A6_frontier_sound`, `A6_remaining_sound`, and `A6_refinedRoster_sound` all report only `[propext, Classical.choice, Quot.sound]`. It is NOT a closure of raw139 or an upper-bound proof for BB(6); all unresolved siblings remain explicit.

`A6Canonical76Ingestion.lean` is the source-accepted live-roster port: it checks that p139 occurs exactly once in the accepted 76-entry roster and applies `graftRoster_sound` to preserve the 7014 quotient dichotomy after replacing that entry by the source-connected A6 frontier. The workflow downloads the accepted canonical76 artifact from run 45647053824 (its artifact label is stale, but exactness job 139320746934 proved `CanonicalTwoParentRosterOnly.exact_at_target` with 76 residuals). Run 45710105710 was an initial interface-argument failure and is superseded by the passing run 45710993495. The successful log reports `p139_rootRow`, `p139_parent_count_76`, `A6_refinedRoster76`, and `A6_refinedRoster76_sound` with only `[propext, Classical.choice, Quot.sound]`. The refined roster's dependent residual cardinality is still unproved.

## Reproduction

The workflow downloads the exact canonical77-certified artifact from run 45554648116, checks out Google DeepMind Cryptids at commit c86f15861709b76042998c5211c7b2f83991621b, updates the upstream Mathlib/Verso pins from Lean 4.35.0-rc4 to 4.36.0-rc2, builds the original A6 machine theorem, and runs reproduce-a6.sh.

The script deliberately uses the Frontier.olean and related dependencies from the canonical77 artifact. It does not mix in the independently built raw117 artifact. The source-connected module is A6Ingestion.lean; its #print axioms reports are part of the CI log.
