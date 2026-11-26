# Fail-isolated Canonical64 parent consumer

## Accepted Canonical59 reduction

Run [45880290680](https://github.com/FlareZ123/bb6/actions/runs/45880290680), source revision `bd64e66c5461f413150d62b6593aa9d071de85d4`, passed the complete source-import, Lean, axiom and fixed-score consumer gate. It integrates five pairwise-distinct parent Covers into Canonical64:

| Parent | Bound | Parent artifact |
| --- | ---: | --- |
| Raw119 | 572 | 15087741037 |
| Raw115 | 7,014 | 15100255568 |
| Raw58 | 3,055,746 | 15090715339 |
| Raw108 | 4,136,180 | 15101731441 |
| Raw118 | 756,496 | 15120592642 |

All five candidates were accepted; none were rejected. The generated module `CanonicalSelectedParentIntegrated.lean`, namespace `BB6.Agent32CanonicalSelectedIntegrated`, proves `countSelected = 59`, `raw59_retained` (the exact Raw59 table remains once in the complement), pairwise distinctness, root compatibility, parent Covers, quotient soundness, and conditional champion-score exactness. The final axiom set is only `propext`, `Classical.choice`, `Quot.sound`; the gate rejects `sorryAx` and `native_decide`.

Generated source SHA256 `38d00088a70b3f290651b40f5f1a4a5e691963c35b9f2c3372e80bfa0d6e80c3`; OLean SHA256 `213f1a6fa5fb7b53a92fbe8385130ef330476eab46e917cce0a4fe2d6a81cc9f`. Full closure artifact [15147189928](https://github.com/FlareZ123/bb6/actions/runs/45880290680/artifacts/15147189928), SHA256 `f19b9977f3e3f3a60c49ae61ad4c5a717689980191bf7ee0d23e7eeff1c27abc`, 5,720,769,280 bytes. See [results/2026-11-26-canonical59-five-parent-integration-agent31.md](../../results/2026-11-26-canonical59-five-parent-integration-agent31.md); the previous [Canonical60 four-parent stage](../../results/2026-11-26-canonical60-four-parent-integration-agent32.md) remains as a traceable predecessor.

This is still conditional on Covers for all 59 retained representatives; it is not an exact BB(6) determination.

## Active incremental candidates

- **Raw113:** source-accepted parent artifact 15108067526, run 45802897709, root `Raw113ParentExact`, theorem `BB6.Agent25Raw113.cover113`, bound 2,674. Exact Canonical64 membership alias/count were added. The delta module `Canonical59Raw113Membership.lean` and theorem `Canonical58Raw113Graft.lean` are prepared. Targeted delta workflow [45882566313](https://github.com/FlareZ123/bb6/actions/runs/45882566313) is now testing Canonical59 → Canonical58 from base run 45880290680; do not claim 58 until its final gate passes.
- **Raw83:** parent Cover artifact 15087730774, run 45755362807, root `A10Raw83Exact`, bound 514. A first membership preflight [45824051367](https://github.com/FlareZ123/bb6/actions/runs/45824051367) failed because an ambiguous `parents` term left `sorryAx` in one helper theorem. The current source qualifies that term; corrected preflight [45881274261](https://github.com/FlareZ123/bb6/actions/runs/45881274261) is still running. No Raw83 cut is accepted yet.
- **Raw59:** Agent32's isolated module relocation / Canonical60-to-59 graft is running in [45878179911](https://github.com/FlareZ123/bb6/actions/runs/45878179911). Do not duplicate or interfere. The Raw59 parent is still present in the accepted Canonical59 roster.
- **Raw106/79/67:** Agent16's source-acceptance run [45878084731](https://github.com/FlareZ123/bb6/actions/runs/45878084731) is still working. Raw106 parent Cover is source-accepted as artifact 15147725126 (root `Raw106ParentCover`, theorem `BB6.Agent10Raw106.parent_cover`, bound 253); Raw67 and Raw79 jobs are pending. Their Canonical64/Canonical59 membership is a separate gate. Avoid rebuilding these parent Covers.

The full-batch fallback script `assemble_canonical_selected.py` contains Raw118 and Raw113 candidate specs, but prefer the incremental delta path to avoid re-running already accepted Covers.
