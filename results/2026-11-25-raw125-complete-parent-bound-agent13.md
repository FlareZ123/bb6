# Source-accepted weighted Cover for the raw125 six-hole cylinder

**Theorem (Lean 4.36.0-rc2, 25 November 2026).** Every completion of

`1RB---_1RC---_0RD---_1LD1RE_---1RF_------`

has a source-verified `Cover (WeightedBound B)` for every `B ≥ 1290`. The first unassigned query is F1 after seven ordinary transitions, and the parent has (25^6 = 244,140,625) compatible completions.

## Proof

The parent split has 26 retained residual obligations: six n-gram certificates and twenty Block-FAR certificates. `Raw125ResidualClosure.lean` verifies the exact residual-table correspondence and closes all 26. The theorem is `BB6.Agent13Raw125.raw125_cover`; its exact axiom profile is `[propext, Classical.choice, Quot.sound]`.

The repaired original-source assembly passed [CI run 45722543448](https://github.com/FlareZ123/bb6/actions/runs/45722543448), job 139584158187, pinned to source commit `779cbab28cf77c823e4a99dc3b358980e7a7f410`. Artifact `raw125-final` (15072483796) contains the 614-module compiled closure. The assembly rebuilt the six n-gram witnesses against the selected cut `SparseZipper` object and compared the differing object's 83 kernel declarations and import descriptors before replaying the final declarations.

The detailed search, cut, residual shards, source commands, and previous failed assembly are documented in `im-results/agent13-raw125/README.md`.

This is a complete bound for one six-hole cylinder, not a global BB(6) upper bound. The alternative canonical77 graft in `CanonicalRaw125Graft.lean` is only a local artifact-backed composition; it is not a source-accepted reduction of the current canonical76 roster.

— Result indexed by Agent 7; proof and research contribution by Agent 13.