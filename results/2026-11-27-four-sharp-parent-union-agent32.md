# Exact weighted maximum of the four F1 sibling cylinders

For the four literal tables `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---{F1}`, the exact local weighted bounds are 379 (0RD), 196 (0RE), 116 (0RF) and 182 (1RF). Each parent has four free slots, hence 390,625 literal completions. The four sets are disjoint (their assigned F1 moves differ), covering 1,562,500 tables altogether. The exact maximum over this union is **379**, including the final halt query and an admissible incoming blank delay. This is an unconditional local theorem, not global BB(6) maximality.

The upper bounds and attainment are supplied by these actual original-source Lean proofs:

| Raw | F1 | Exact bound | Theorem | Successful proof artifact |
|---|---|---:|---|---|
| 95 | 0RD | 379 | `BB6.Agent31SharpRaw95.exact95` | 15164121806 |
| 99 | 0RE | 196 | `BB6.Agent2Raw99.exact99` | 15166288975 |
| 103 | 0RF | 116 | `BB6.Agent3Raw103.exact103` | 15163277898 |
| 105 | 1RF | 182 | `BB6.Agent31SharpRaw105.exact105` | 15164195888 |

Raw95/103/105 passed their independent jobs in [run 45919568346](https://github.com/FlareZ123/bb6/actions/runs/45919568346), revision `fc71d53353958fd92100191242692dbcbfe00360`. That aggregate run failed only at Raw99's padding lemma. The corrected original Raw99 source passed [run 45926296755](https://github.com/FlareZ123/bb6/actions/runs/45926296755), revision `2495b790e8650dd55a007ce950329f8530a55c9f`; all 76 modules checked. Its attaining completion is `1RB0RD_1RC1LF_0RDHHH_1LD1RE_1RB0LB_1LA0RE`, with 195 ordinary transitions, delay zero, and final C1 query.

[FourSharpCover.lean](../im-results/agent32-four-sharp/FourSharpCover.lean) imports the four accepted original roots. It proves the four exact literal-table equalities, disjointness of the F1 choices for any compatible completion, a `Cover (WeightedBound B)` for every one of the four literal parents whenever `379 ≤ B`, and

```lean
theorem union_exact (B : Nat) :
    (∀ m, (∃ p ∈ parents, compatible p m) → WeightedBound B m) ↔ 379 ≤ B
```

The union theorem was freshly checked locally on Lean 4.36.0-rc2 against the downloaded original-source objects. All 159 distinct project object files link without any byte-different shared module. The exact source SHA-256 is `da73bcc201761af389031ad06d321cd988658b5aa4089aa89f760bb62be7a465`. Every equality and the disjointness proof use only subsets of `[propext, Quot.sound]`; the Cover and sharp union proofs use `[propext, Classical.choice, Quot.sound]`.

Reproduce by extracting the `parent/*.olean` files of the four named artifacts into one directory, rejecting any unequal overlapping file, and running `LEAN_PATH=. lean -o FourSharpCover.olean FourSharpCover.lean` in that directory with the pinned Lean version. Artifact ZIP SHA-256 digests:

- Raw95: `e92d33dd6dffa3bf8acf7cd5cd2d90e9f08a00c4fed5581615ea45e71ae0aebe`.
- Raw99: `c8c88c253f130b162f9c7b3f99ebe7dedafb0af24ab14261b56c0c9d95e8673b`.
- Raw103: `092804dd1873c2db40247ce33c06f14234cad8e62f257f07fc488e819f4f7551`.
- Raw105: `53fd0f80323fca1cd4b6afeebbb89ff7813be83acb3527437d64e8558d0039a9`.

**Integration boundary:** the four parents are now consumed on the accepted Raw124 Canonical57 lineage. [run 45962202844](https://github.com/FlareZ123/bb6/actions/runs/45962202844) checked unique membership, pairwise distinctness, all four removals, the 53-entry complement and fixed-score exactness, and exported [artifact 15181258095](https://github.com/FlareZ123/bb6/actions/runs/45962202844/artifacts/15181258095) before the subsequent seven-ready phase failed. The conditional theorem still requires all 53 retained Covers, including Raw59. See the [acceptance note](../communications/broadcast/20261127T1145Z_Critic-accept-canonical53-and-unblock-seven-ready.md).
