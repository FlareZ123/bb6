# q_i(2,32) checkpoint containment

This is an intermediate source-bridge result, not a BB(6) upper-bound proof.

## Accepted finite containment theorem

The exact 32-update checkpoint `SearchQueue_upds decider (q_i 2 32) 32` has 84 active nodes. All 84 are descendants of the canonical first-one residual at canonical roster index 7 (raw residual index 11), whose source table is:

```
1RB---_1RC---_0LA---_------_------_------
```

The parent has depth 2 and nine holes. The Coq file `Agent44Q32CanonicalParent.v` proves:

- `q32_active_count`: exactly 84 active nodes;
- `q32_active_refines_canonical_residual_7`: every decoded node is a source `is_child_of` refinement of the literal parent table;
- `q32_checkpoint_refines_canonical_residual_7`: the result transfers to the exact queue checkpoint using `packed_chunk_2_32_32_exact`;
- `q32_canonical_residual_7_extends_root` and `q32_checkpoint_refines_root`: the parent and checkpoint remain inside the original root cylinder;
- `q32_canonical_residual_7_source_roundtrip`: the original Coq parser/serializer roundtrip holds pointwise for the parent table.

The focused original-source Coq gate `enumerate62-q32-canonical-parent` passed in CI run [45501470506](https://github.com/FlareZ123/bb6/actions/runs/45501470506). This establishes containment only; it does **not** establish that the parent or its descendants are nonhalting or weighted-safe.

## Remaining source obligations

An existing finite cross-match reports 34 source certificates (32 side-cycle certificates and two sweep cases), leaving 50 unresolved descendants. Their hole-count histogram is 3:9, 4:3, 5:6, 6:10, 7:22; none is a one-hole node.

`Agent44ChunkSideSearch.v` now first searches the nine-hole parent for a single source-side cycle witness. If one is found, it can cover the entire 84-node checkpoint and the descendant search is skipped. Otherwise it searches the 50 remaining nodes with the existing bounded grid (directions L/R, entry 0–12, period 1–13, budget 0–2).

`Agent44Q32ParentSideProbe.v` is a lightweight, source-only probe of that parent-level grid; it avoids the currently blocked weighted-source dependency. Its result is pending CI.

## Boundary

No safety result for the 50 descendants is claimed. The global 124-residual upper-bound programme remains open. Keep all unfinished work in `im-results/`; promote nothing here to `results/` until the mathematical closure is complete and independently auditable.
