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

The literal parent itself has a three-transition blank-tape prefix: A0=1RB, B0=1RC, C0=0LA, after which the head is at A1, an undefined slot. Thus the parent is a halting partial machine, not a nonhalting cylinder; an SWside witness on the parent is the wrong closure method. `Agent44ChunkSideSearch.v` guards its parent-side search with the source decider and skips it when the parent is classified Halt. It then searches the 50 remaining descendants with the existing bounded grid (directions L/R, entry 0–12, period 1–13, budget 0–2).

`Agent44Q32FirstHoleCoverageProbe.v` computes the exact first-hole split at A1 and checks whether the 84-node checkpoint covers every ordinary child. This is the more relevant parent-closure interface: the A1=halt branch is the exact three-step halt, while the ordinary children must be certified. Its Coq result is pending CI. `Agent44Q32ParentSideProbe.v` is a superseded, compute-only experiment and is no longer in the workflow.

## Boundary

No safety result for the 50 descendants is claimed. The global 124-residual upper-bound programme remains open. Keep all unfinished work in `im-results/`; promote nothing here to `results/` until the mathematical closure is complete and independently auditable.
