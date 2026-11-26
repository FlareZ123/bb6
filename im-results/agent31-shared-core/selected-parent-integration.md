# Fail-isolated Canonical64 parent consumer

## Accepted Canonical60 reduction

Run [45876657378](https://github.com/FlareZ123/bb6/actions/runs/45876657378), source revision `3f923338bb7a95403a8fa089741f59ad892d4e70`, passed the full compile, axiom and fixed-score consumer gate. It independently integrated Raw119, Raw115, Raw58 and Raw108 at common weighted floor 6,766,859. All four candidates were accepted; none were rejected.

The generated module `CanonicalSelectedParentIntegrated.lean`, namespace `BB6.Agent32CanonicalSelectedIntegrated`, proves:
- `countSelected`: exactly 60 representatives remain from the accepted Canonical64 roster;
- `raw59_retained`: the exact Raw59 table occurs once in the complement;
- pairwise distinctness, root compatibility and the four parent Covers;
- `sound_integrated`, then `exact_at_champion_score`, conditional only on Covers for all 60 retained representatives.

Parent bounds: Raw119 572; Raw115 7,014; Raw58 3,055,746; Raw108 4,136,180. The proof gate checked the literal parent equalities, unique Canonical64 membership, imported source closures, and final theorem profiles. Final axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide`.

Generated source SHA256 `dd3386fcfdb80197eb558985642c6f13aaff85351531bd848f0423bbd0750996`; OLean SHA256 `d538c5479fb948c59f00e5735673884dec86abaec79b702ea2e6f6ba3ba5ba1e`. Full closure artifact [15146101833](https://github.com/FlareZ123/bb6/actions/runs/45876657378/artifacts/15146101833), SHA256 `68b3819703aa7d131a6e2021b083760e8e555ee499357c73b4b95931002860b6`, 5,129,452,624 bytes. See the academic result [Canonical60 four-parent integration](../../results/2026-11-26-canonical60-four-parent-integration-agent32.md) and the report [canonical60-selected-integration.json](../agent32-raw59/canonical60-selected-integration.json).

## Next parent candidates

### Raw118 — prepared, not yet integrated

- Parent Cover: run 45812415227, artifact 15120592642 (`raw118-parent-proof`), theorem `BB6.Agent1Raw118Complete.parent_cover`, root `Raw118Complete`, bound 756,496.
- Unique Canonical64 membership: run 45845180631, artifact 15131232543, theorem `BB6.Agent16Raw118Canonical64Membership.p118_parent_count64`.
- Exact table: `1RB---_1RC---_0RD---_1LD1RE_---0LE_------`.
- The selected-parent assembler includes this candidate and recompiles `Raw118Canonical64Membership.lean` after importing the parent closure. Candidate addition commit: b9c3ea3a. The next `canonical64-selected-parent-batch` run must pass before changing the accepted count from 60.

### Concurrent parent work

- Agent16 is checking Raw106/79/67 membership in run 45878084731. Wait for source-accepted theorem names and exact artifact metadata before adding them.
- Agent32 is testing the isolated Raw59 module relocation and Canonical60-to-59 graft in run 45878179911. Do not duplicate Raw59 while that integration is active.

This remains a conditional upper-bound interface, not an exact BB(6) result.
