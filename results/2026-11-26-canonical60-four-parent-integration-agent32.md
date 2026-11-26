# Canonical60: accepted four-parent reduction and fixed-score consumer

**Accepted 2026-11-26.** The fail-isolated Canonical64 consumer independently integrated the exact parent Covers of Raw119, Raw115, Raw58 and Raw108 at common weighted floor 6,766,859. The final original-source Lean consumer passed in run [45876657378](https://github.com/FlareZ123/bb6/actions/runs/45876657378), job 140105341513, source revision 3f923338bb7a95403a8fa089741f59ad892d4e70. The theorem leaves exactly **60** quotient representatives. Raw59 remains exactly once in the complement. No exact BB(6) value or unconditional global upper bound follows.

## Theorems
Generated module CanonicalSelectedParentIntegrated.lean, namespace BB6.Agent32CanonicalSelectedIntegrated:
- selectedParents consists of exactly p119, p115, p58, p108; all source table equalities, membership counts, pairwise distinctness and weighted Covers were checked.
- countSelected: rosterSelected.length = 60.
- raw59_retained: the filter by exact p59 table has length 1.
- sound_integrated: every compatible root completion is either WeightedBound 6766859 or TNFQuotientCompatible with a remaining representative.
- exact_at_champion_score: if every retained representative has Cover (WeightedBound (proposedTM63Moves + 7)), then ExactBB6 (proposedTM63Moves + 7), using the accepted exact blank-start champion witness.

The four accepted local bounds are respectively 572, 7,014, 3,055,746 and 4,136,175; the source gates lift each to the common floor. The proof combines independently source-accepted Covers and checks exact common kernel declarations, not numerical evidence or an assumed count. All final axioms are within propext, Classical.choice, Quot.sound; no sorryAx/native_decide.

## Reproduction and downstream consumption
- Workflow: .github/workflows/agent31-canonical71-raw109.yml, target canonical64-selected-parent-batch; exact source revision above.
- Producer script: im-results/agent31-shared-core/assemble_canonical_selected.py.
- Final artifact [15146101833](https://github.com/FlareZ123/bb6/actions/runs/45876657378/artifacts/15146101833), SHA256 68b3819703aa7d131a6e2021b083760e8e555ee499357c73b4b95931002860b6, size 5,129,452,624 bytes. Includes linked proof closure, generated sources and integration report.
- Generated consumer source SHA256 dd3386fcfdb80197eb558985642c6f13aaff85351531bd848f0423bbd0750996; olean SHA256 d538c5479fb948c59f00e5735673884dec86abaec79b702ea2e6f6ba3ba5ba1e.
- Full report extracted from successful job output: [Canonical60 report](../im-results/agent32-raw59/canonical60-selected-integration.json).
- This is a direct successor to the accepted Canonical64 interface. Any future parent integrations must remove only independently checked exact members of this complement, or reconstruct a direct-from-64 combined complement without double-counting.

Raw59's earlier source-certified exact local bound is not yet included because its width-two module implementation differs from the canonical legacy one. The independent targeted native declaration-relocation CI 45878179911 tests that next edge. Other remaining parents and hard-root decisions are still required.
