# Exact forward-orbit audit of the t=3 high-q gate through 100,000

**Status:** reproducible finite computation; not a universal root-exclusion theorem.

Script: [t3_high_gate_forward_audit.py](t3_high_gate_forward_audit.py)

## Result

The script enumerates every source-margin-admissible (t=3) high-q candidate in the sectors (n\bmod6\in\{4,5\}), for (20\le n\le100000). It then compares each candidate with the unique deterministic reset-height orbit starting at the blank-root reset height 2.

| Quantity | Exact result |
|---|---:|
| Maximum index (n) | 100,000 |
| High-q candidates checked | 245,399 |
| Root reset edges through first height with bit length 100,001 | 129,311 |
| Candidate/root-orbit matches | **0** |
| Second-parent (r\bmod3=0) candidates | 81,747 |
| Second-parent (r\bmod3=1) candidates | 81,859 |
| Second-parent (r\bmod3=2) candidates | 81,793 |
| Largest candidate depth (j) | 99,736 |

The exact stream digests are:

- Candidate stream SHA-256: `b99cf74d68f721420c21baf1f8b1de2024bccda2ced35fe145adab6729aa758c`
- Root-orbit prefix SHA-256: `7dd54a54bfae2ad7d9409e35e1b74f5537be4a725a01f661274b7bd48e40f536`

The script uses arbitrary-precision integer arithmetic throughout. It validates its binary-search implementation of the first-reset sweep index against the original linear scan for every height from 2 through 10,000, and validates the algebraically rearranged source-margin cutoff against a direct search for every (n\le10000).

## Why the finite exclusion is exact

The source-C first-reset semantics are formalized in:

- [FirstOutcome.lean](../agent10-cascade/FirstOutcome.lean): `closed_outcome`, `outcome_unique`, and `first_reset_classification`.
- [FirstInverseComplete.lean](../agent10-cascade/FirstInverseComplete.lean): `reset_parent_iff`, the complete even/odd first-reset inverse grammar.
- [ResetParentStrict.lean](../agent10-cascade/ResetParentStrict.lean): `reset_parent_strict`, proving every successful reset strictly increases the height.

These source modules were compiled in [CI run 41892190566](https://github.com/FlareZ123/bb6/actions/runs/41892190566). The high-q candidate selector and precision-nine second-parent selector were independently source-checked in [CI run 42404919018](https://github.com/FlareZ123/bb6/actions/runs/42404919018).

The orbit scan is complete for this finite range: the reset map is deterministic, every successful reset increases the height, and every candidate at index (n) lies in the (n)-bit high-q band. Once the root orbit passes that bit length, it can never return to any candidate in that band.

The precision-nine counts agree with the formal selector in `TranslatedDepthResidue.lean`: the (r\bmod3=0) cases are exactly the candidates satisfying the unique translated (3^9) condition. This does not resolve the (r\bmod3=1,2) branches for arbitrary (n), and it does not prove a universal exclusion for all indices.
