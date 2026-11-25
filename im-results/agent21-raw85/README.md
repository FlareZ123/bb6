# Raw85: complete four-hole cylinder bound

## Established result

The partial table
`1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1RA`
has a complete original-source Lean weighted bound of **7014** for every compatible six-state machine. The full parent-tree audit passed in [run 45548434985](https://github.com/FlareZ123/bb6/actions/runs/45548434985), revision `aed5e0175fe32165f13d9b849c4a2d5cd3273dac`. The audited theorem is `BB6.Agent31FourHoleSibling.all_completions_weighted`; the workflow checks the actual generated path-end table against the literal twelve-slot parent and rejects `sorryAx` or `native_decide` in the final audit.

This is raw residual 85 (manifest entry 54), a four-hole parent in the 124-table first-one roster. Its complete certificate is stronger than any individual FAR hit or sweep witness. **It has not yet been ingested into the accepted canonical77 quotient roster.** No new global residual count is claimed.

## Certificate construction

The deterministic dynamic first-hole tree has 24 ordinary children per split and charges the halt branch using the source weighted-query checker. Its nonhalting leaves use source-checked side cycles, destination-saturated FAR certificates, or exact parametric sweeps. Agent 40 supplied the three missing sweep families, with positive return costs 93+36n, 113+76n and 20+44n; see [the sweep derivation](../agent40-raw85-sweeps/README.md). Every proved sweep is matched against the actual twelve-slot table by the source audit, not by its search key.

The original finite search census was 3,774 cycle leaves, 1,761 last-hole leaves, 245 split nodes and 101 open leaves. The old DFA bank plus 14 canonical candidate strings and five exact-target SMT candidates supply the FAR candidates; [the SMT run provenance](smt-candidates-provenance.md) records five hits and three misses. Those three misses are now covered by the sweeps. The historical `Raw85FARCertificates.lean` scratch module failed CI 45503416279 and is excluded from the accepted proof. The candidate files are untrusted search data; the source `Audit.check` verifies all final leaves, including the start-zero condition.

## Shared-core ingestion

The raw85 wrapper now emits uniquely named `Raw85Sibling*.lean` and a separate `Raw85SweepData.lean` containing only the three new sweep proofs. This deliberately avoids changing the shared core's older `SweepData` module or colliding with the generic `FourHoleSiblingData` name used by other siblings. The pinned canonical core revision d4164a4457e62ba7ec8e3fba6e38b251d04ffc83 has only the original M0–M9 sweep list, whereas the successful raw85 run used M10–M12 as well.

- `Raw85Bound.lean` exposes the literal-parent all-completions theorem after exact path-end equality.
- `Raw85CanonicalCut.lean` defines a score-parametric exact-table graft, with a proposed check that the original 96 canonical representatives become 95. It has no champion imports.
- Reproduce the generated source by running `python im-results/agent13-coverage/unpack.py` and `python im-results/agent13-roster-convergence/generate_raw85.py` from the repository root. The latter uses the existing sibling and sweep generator functions, with the explicit three raw85 sweep tables. A shared-core build can use this generator even with the older M0–M9 sweep list.
- The existing manual raw85 workflow now checks the renamed parent source closure and publishes a manifest and compiled objects. The renamed modules and generic cut remain pending source acceptance; the prior successful original-name theorem is unaffected.

The integration owner should batch this cut with the other accepted parent proofs using the validated common Lean objects. Check the actual resulting roster length and transitive axiom profile. The remaining residual Covers and universal BB(6) upper bound remain open.
