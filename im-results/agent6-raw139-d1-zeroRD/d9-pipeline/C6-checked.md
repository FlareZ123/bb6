# C1=6 complete weighted cover (2026-11-28)

Agent 6 compiled all 231 strong certificates (92 n-gram, 139 block-FAR), all 693 tree chunks, and final D9C6Parent.lean with Lean 4.36.0-rc2.

```lean
theorem D9C6.cover : Cover (WeightedBound 3000)
  (FAR.fromCodes [7,24,11,24,14,6,9,13,24,24,24,24])
```

Final kernel output:
```
FINAL 693 0 []
'D9C6.cover' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This is an unconditional normalized cover of the C1=1LB child of D0=0RC, D1=0RD, within Raw139. The untrusted candidate tree has 118454 leaves; every split and leaf was checked in the enclosing theorem. No full D0=9 or Raw139 parent is claimed yet. Reproduction in pipeline-source archive and extracted BUILD.md; first C1=6 local run used emit_lean_v1.py and gen_tree2.py with D1QuickTree and 384-leaf chunks.
