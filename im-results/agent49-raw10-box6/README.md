# Raw10 rectangle 6: source-accepted exhaustive Cover

## Exact domain and mathematical result

The original base-34 rectangle fixes A0..D1 to codes 8,14,11,7,17,4,9,2 and excludes 23 at E0. E1/F0/F1 are unrestricted. This is 375,000 tables, disjoint from rectangle 7. Code 0 is halt, -1 is a hole, and 1+4q+2w+r is an ordinary transition.

**Source-accepted result:** every completion of this exact source rectangle has ordinary halting score at most 70, hence weighted first-one bound at most **75** after allowing at most five initial blank-delay steps. The source consumer also exports the exact residual consumer `residual_without_box6`, so this rectangle can be removed from the source-indexed Raw10 remainder while retaining every other box.

## Original-source Lean acceptance

- **Successful run: [45893206793](https://github.com/FlareZ123/bb6/actions/runs/45893206793).**
- Source revision: `c0dafc606f26fccb08a97b30c199905bbbe4464f`.
- Toolchain: Lean 4.36.0-rc2.
- The original-source closure compiled **94 project modules**, including `Box6Core`, `Box6Hard`, all 25 generated shards, and `Box6SourceConsumer`.
- Accepted declarations:
  - `BB6.Agent49Box6.treeCheck_sound`
  - `BB6.Agent49Box6.base_ordinary`
  - `BB6.Agent49Box6.ordinary_weighted`
  - `BB6.Agent49Box6.externalCheck_sound`
  - `BB6.Agent49Box6.box6_ordinary`
  - `BB6.Agent49Box6.box6_weighted`
  - `BB6.Agent49Box6.raw10_box6_closed`
  - `BB6.Agent49Box6.residual_without_box6`
- Every exported theorem above has only `propext`, `Classical.choice`, and `Quot.sound` in its axiom profile. The workflow explicitly rejects `sorryAx` and `native_decide`.

The earlier run [45829991506](https://github.com/FlareZ123/bb6/actions/runs/45829991506) failed at a proof-script elaboration defect in `Box6Core.lean`: an `intro a ha` was applied to the terminal equation `run m (n+1) blank = none`, which has no binders. This was not a counterexample. The corrected `fix_emitter.py` now proves the one-step halt directly by changing the goal to `((run m n blank).bind (rawStep m)) = none`, rewriting the known prefix run, and simplifying `rawStep` with the exact queried slot and halt hypothesis. The successful run removes the prior `sorryAx` profile.

## Reproduction

The original discovery partition has 479 internal nodes, 479 halt leaves (maximum ordinary score 70), 3,561 exact cycles, 4,866 left translated cycles, 2,047 right translated cycles, and 356 open leaves. Of those, 318 are all-ordinary total tables, 36 are closed by bit n-grams, and two are closed by 45-state two-cell block n-grams. The two remaining partials are closed by finite three-cell BlockFAR saturation.

The proof archive `proof-source.tar.xz` contains `Box6Core.lean` and `emit_box6.py`. The manual target `weighted-tnf-raw10-box6` in `.github/workflows/agent13-coverage.yml`:
1. unpacks the original source and proof archives;
2. applies `fix_emitter.py` to the emitter and generic checker;
3. regenerates the sparse partition, n-gram certificates, and BlockFAR certificates;
4. compiles the exact source consumer against the repository's original machine model.

The generator and finite search are untrusted; the accepted result comes from the Lean kernel checking the complete source closure. The accepted source theorem is a **partial parent Cover**, not a complete Raw10 parent Cover or a global BB(6) upper bound.

## Remaining obligations

- The other 33 original base-34 rectangles, the separate held leaf, and the other root-roster obligations remain.
- Exact Canonical59 membership/consumption of the B0=1LC parent is not established by this result.
- A reusable dependency-closed proof artifact and manifest are being added to the existing manual workflow; the accepted source theorem does not depend on that transport step.
