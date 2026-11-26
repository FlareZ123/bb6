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

- **Raw113:** parent artifact 15108067526, run 45802897709, root `Raw113ParentExact`, theorem `BB6.Agent25Raw113.cover113`, bound 2,674. First delta attempt [45882566313](https://github.com/FlareZ123/bb6/actions/runs/45882566313) passed membership but exposed a noncomputable-base alias in the final source. The alias is fixed in commit 2991aea0. Retry [45883294480](https://github.com/FlareZ123/bb6/actions/runs/45883294480) compiled the full 58-residual theorem and printed the standard-axiom report, but failed only because the workflow tested the OLean at the wrong path, so no artifact was uploaded. The corrected shared-workflow retry [45884968665](https://github.com/FlareZ123/bb6/actions/runs/45884968665) is now running with the proper OLean path and artifact preservation.
- **Raw83:** parent Cover artifact 15087730774, run 45755362807, root `A10Raw83Exact`, bound 514. Corrected membership preflight [45881274261](https://github.com/FlareZ123/bb6/actions/runs/45881274261) passed, artifact 15148790096 (SHA-256 `a9150b5c69395095180aef47466c990b76bed1bacdcfcbb5fc9c84853eb57e80`). It proves unique membership in Canonical64 and the earlier five-/six-parent Canonical59/58 rosters with standard axioms. The new source `Canonical58Raw83Membership.lean` rechecks membership against the Raw118-based Canonical58 roster; `Canonical57Raw83Graft.lean` and its script are prepared. Target `canonical57-raw83-delta` is consolidated into the existing `.github/workflows/agent31-canonical71-raw109.yml`; dispatch only after Raw113 delta succeeds.
- **Raw59:** Agent32's isolated module relocation / Canonical60-to-59 graft is running in [45878179911](https://github.com/FlareZ123/bb6/actions/runs/45878179911). Do not duplicate or interfere. Raw59 remains in the accepted Canonical59 roster.
- **Raw106/79/67:** Agent16 run [45878084731](https://github.com/FlareZ123/bb6/actions/runs/45878084731) is still working. Raw106 source accepted as artifact 15147725126 (root `Raw106ParentCover`, theorem `BB6.Agent10Raw106.parent_cover`, bound 253); Raw79 source accepted as artifact 15148575654 (root `Raw79ParentCover`, theorem `BB6.Agent10Raw79.parent_cover`, bound 2,354); Raw67 compiled its parent theorem with standard axioms but job 140110185934 ended with runner shutdown (exit 143) before artifact upload; this is not a proof failure. Membership remains a separate gate. Agent16 has been asked for a focused Raw67 rerun and exact aliases.

Prefer incremental deltas from accepted rosters; avoid rebuilding already accepted parent Covers.
