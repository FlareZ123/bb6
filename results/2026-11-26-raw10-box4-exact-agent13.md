# Exact weighted maximum of Raw10 rectangle 4

Agent 13 — 2026-11-26. **Source-certified.**

For the source-defined rectangle `raw10Remainder[4]!`, the first six transition codes are [8,14,11,7,17,4], D0 excludes code 9, and the remaining five slots are unrestricted. Its cardinality is 24·25^5 = 234,375,000. The exact weighted maximum is **3640**.

The machine [8,14,11,7,17,4,23,2,20,15,5,0] attains this value: 3639 live steps, one halt step, zero incoming blank delay. The weighted bound is the repository's source-defined `WeightedBound`, including the incoming blank-delay correction.

## Theorems
```lean
BB6.Agent13.Box4.sourceBound :
  ∀ m, Fits raw10Remainder[4]! m → WeightedBound 3640 m

BB6.Agent13.Box4.sourceExact (B : Nat) :
  (∀ m, Fits raw10Remainder[4]! m → WeightedBound B m) ↔ 3640 ≤ B
```

## Proof
The exact one-halt reduction yields 46,116,864 representatives in six disjoint designated-halt slices. Exhaustive first-hole trees use checked finite halts, translated cycles, stack automata safe boxes (including lag/RLE invariants), and block-FAR certificates. Each slice root is independently source-checked; the parent composition uses the source-domain equality and exact lower witness. All six slices passed the [matrix run](https://github.com/FlareZ123/bb6/actions/runs/45824867779). The [parent assembly](https://github.com/FlareZ123/bb6/actions/runs/45848274779) reused 544 hash-verified dependency-closed modules, compiled the 545th module, and accepted both exported theorems with only propext, Classical.choice, Quot.sound. The proof source and manifest are in [artifact 15132561361](https://github.com/FlareZ123/bb6/actions/runs/45848274779/artifacts/15132561361).

Reproduction: [Box4 directory](../im-results/agent13-raw10-box4/README.md), manual workflow weighted-tnf-raw10-box4-sliced-full, or weighted-tnf-raw10-box4-assemble-existing using source run 45824867779.

This closes one Raw10 residual rectangle. It does not yet close Raw10 or reduce the global canonical roster count.
