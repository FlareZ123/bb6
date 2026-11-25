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

`Agent44Q32FirstHoleCoverageProbe.v` now compiles in the original BusyCoq Coq environment (CI run 45517921880). The parent decider returns `Halt (A,1)` after the three-transition prefix A0=1RB, B0=1RC, C0=0LA. Its normalized first-hole expansion has 16 children.

The exact ordered child-decider vector is:

```
[NonHalt, NonHalt, Halt, NonHalt, Halt, NonHalt, Halt, NonHalt,
 Halt, NonHalt, Halt, NonHalt, Halt, Halt, Halt, Halt]
```

There are 7 `NonHalt` and 9 `Halt` partial-machine branches. The probe proves the corresponding child classification and uses the existing `agent32_decider_bounded_sound` theorem for the soundness adapters. `Print Assumptions` exposes that theorem's existing profile, including Coq primitive-integer/array constants and `inj_pair2`; this is not an assumption-free academic result.

Crucially, `q32_parent_children_coveredb = false`: only two of the 16 children have descendants in this particular q32 active slice, namely A1=1LD and A1=1RD. The 84 active nodes split exactly into 14 descendants under A1=1LD and 70 under A1=1RD; no active node leaves A1 undefined or uses another transition. Thus this checkpoint is a local slice, not a complete cover of the parent cylinder. Of the 14 absent children, 7 are the decider's `NonHalt` cases; the other 7 are `Halt` partial branches whose descendants must be accounted for in other global queue slices.

The separate 50-node first-hole split in `Agent8Chunk2FirstHole.v` is a different decomposition: it produces 1,200 child obligations from the 50 unresolved post-certificate nodes. That module still awaits a successful source-roster CI run because of the Agent47 source-witness dependency. The new `Agent44Q32RemainderBranchProbe.v` is queued in the source-roster target to quantify the 50 unresolved nodes by A1 branch. 

## Decider-first full-parent source tree (pending CI)

The q32 parent is not safely closed by the 84-node checkpoint alone. A new generic alternative is in `Agent44Q32DeciderTree.v`:

- A `NonHalt` verdict closes the current cylinder through `agent32_decider_bounded_sound` and `source_nonhalt_cylinder`.
- A `Halt h` verdict with exactly one undefined transition closes through `source_last_hole_cylinder`.
- Other `Halt h` verdicts split on every member of the complete `source_moves` list, using the actual bounded halt trace returned by the decider soundness theorem.
- `Unknown` and depth-limited `Halt` nodes remain in an explicit open frontier.

The generic soundness theorem is conditional on safety of that frontier and applies at any bound at least 1,000,006. The q32 instance computes a depth-2 frontier. This is a complete parent-cylinder decomposition at the source-tree level; it does not assume that the q32 queue slice covers the other first-hole branches. CI target `enumerate62-q32-decider-tree` is run **45538177877**, last observed in progress. No frontier count or safety closure is claimed until it completes successfully.

A second integration audit is in `Agent44Q32ParentTreeIntegration.v`. It checks whether Agent50's parent-tree open leaves are covered by the original 34-node roster, the newer side-search roster, or the surviving q32 queue residuals, using the actual source-refinement relation rather than comparing list lengths. If the coverage boolean is true, a conditional parent-safety theorem follows from safety of the remaining queue nodes. CI target `enumerate62-source-first-hole` is run **45537676191**, last observed in progress; the coverage boolean has not yet been accepted.

The deeper 1,200-child side-search attempt was cancelled and is not a result. Its optimized source module remains experimental. All of these source-tree theorems are Coq-side and still require a separate Lean bridge before they can discharge a Lean `Cover (WeightedBound B)` obligation. The existing `WeightedTNFCertificate` constructors suggest a route (nonhalt, last-hole, expand), but no Coq-to-Lean proof transfer has been established.

## Boundary

No safety result for the 50 descendants is claimed. The global 124-residual upper-bound programme remains open. Keep all unfinished work in `im-results/`; promote nothing here to `results/` until the mathematical closure is complete and independently auditable.


### S4 orbit-cover audit

The exact roster is not closed under all root-fixing S4 permutations, but exact closure is stronger than necessary. See [Agent44S4OrbitCover.md](Agent44S4OrbitCover.md) and the self-contained Lean proof [Agent44S4OrbitCover.lean](Agent44S4OrbitCover.lean) for the generic safety-direction cover theorem and the q32 example. In particular, the three nonidentity q32 images refine raw152/raw156/raw160, which themselves lie in one exact orbit.

The reproducible finite audit is [orbit_cover_audit.py](orbit_cover_audit.py). It checks all 24 S4 images of every residual against the exact-orbit representatives and against the full roster, then computes a greedy cover upper bound. Its CI runner is [s4-orbit-cover-audit.yml](../../.github/workflows/s4-orbit-cover-audit.yml). A successful audit is computational evidence for the finite cover relation; a kernel-checked theorem must still encode the resulting cover map.
