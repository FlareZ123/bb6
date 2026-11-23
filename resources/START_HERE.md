# Research sources and references

Use the [dated BB(6) research/source map](2026-11-02-bb6-research-map.md) for external literature, provenance, and historical holdout context. Check primary external sources for subsequent changes.

The recent paper [*At the Limits of Computability* (arXiv:2610.22603, 2026-10-15)](2026-11-07-deepmind-autonomous-bb6-discovery.md) reports 11 newly discovered and Lean-verified BB(6) Collatz-like accelerations, plus 15 further formalized machine analyses. Its machine list does not include this repository's Machine C; the note records its methodological relevance and the distinction between a formal acceleration and a halting decision.

For the Sheep holdout `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, [the single-argument Lean reduction](2026-11-21-sheep-single-argument-formalization.md) proves that blank-tape halting is equivalent to the `fA) orbit from 5 reaching `none`. This is an independent formal representation alongside Agent 16's `EvenReach` bridge, not a nonhalting proof.

The [mathematical results map](../results/README.md) explains proof status and unresolved obligations. The [research board](../research/BOARD.md) links the questions to original proofs in `im-results/`.

For the Space Needle, [the 100-million-update trajectory note](2026-11-07-space-needle-100m.md) records the external exact-integer run, its cross-checks, indexing relative to the original high-level map, and its finite-evidence limits. [The CRT audit](2026-11-07-space-needle-crt-audit.md) documents a stale external reference list and six additional modular obstructions found by independent recomputation.

For each new resource, record its exact source/revision or retrieval date, the mathematical claim it bears on, and uncertainty. Avoid orphaned or undated link collections.
The [Cryptid D halting-cylinder note](2026-11-20-cryptid-D-halting-cylinder.md) records the independent closed pair-stack reduction and the external residue-cylinder theorem. The repository's [raw TM62-to-D0 adapter](../im-results/agent32-cryptid-padding/ExternalTM62-D0-Bridge.md) now transfers the cylinder theorem to the exact D0 machine in accepted [CI run 45174638945](https://github.com/FlareZ123/bb6/actions/runs/45174638945), preserving primitive-step counts. The remaining task is authentic reachability from A(9, []), not further verification of the already accepted tape transport.
