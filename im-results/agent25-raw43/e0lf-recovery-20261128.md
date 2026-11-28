# Local recovery of Raw43 B1LE E0LF

Agent25, 2026-11-28, completed 18:52 UTC.

## Kernel result

Lean 4.36.0-rc2 accepted `BB6.Agent25Raw43B1LE_E0LF.all43child`:

```lean
theorem all43child : ∀ m, compatible p43child m → WeightedBound 423 m :=
  certificate43child.sound
```

Its axiom report is exactly:

```
'BB6.Agent25Raw43B1LE_E0LF.all43child' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The root is the partial table `1RB---_1RC1LE_0RD---_1LD0RB_0LF---_------`. This is a local mathematical closure of this cylinder, not yet an accepted CI parent or a Canonical38 count decrement.

## Reproduction

- Exact Lean binary SHA256 db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00.
- Run 46162375708, source e2548983547c7026f684962c94ac0b4d0b81bd4c: all 15 successful BiDFA artifacts; 58 batch roots, 65 distinct modules, 346 machine certificates. The failed assembly assigned batches lexicographically while producers used numeric order. Every one of the 15 artifact root sets agrees with numeric modulo assignment. All object hashes and shared module identities were verified.
- Run 45994150694 (E0LC child) supplies the common proof modules; run 46161969966, artifact 15270127869 supplies E0LF M559. M1106 is exact source blob 3088c3bc095f9725061cf4820e489efdeddaa707 and was compiled locally against identical dependencies.
- Exact enumerator `fast_partition.cpp` blob 004d096513b096e830846dcd71324db548f0bab7, cap=1000, lookback=32. Enumerates 2079 open, 54814 cycles, 19859 last, 3337 split; total physical mass 9,765,625. Tree open SHA256 94b8b616eecad2efd40224c8e720a230d466fbc211690d983fa69cb5e878900e; tree JSON SHA256 1c0354c98fff3e52da6f7ccdfdd911425ed81ea2f3b13e6e270bc8878b637fb4.
- Reconstructed all remaining 1731 FAR leaves with the actual mask algorithm, trying the 11 existing witness codes in increasing length: 00101,000,1012101,100,001213321,0012101,00112344444,1012121,1010202,0010202,1012111. The generated tree used chunks of 240 and shard sizes 5000, with 217 tree modules; every module passed. The final Data source SHA256 263174fd12f1290e7f20245c1069c17eb9d2f01a21097d512c1effb6b5cb156b; object SHA256 00b8e58e92fc779b2d1e22e355a45a23139a33ec96d82a92c1fa5cf10b4b5487.

The canonical CI reproduction uses existing `agent10-four-hole.yml` target `raw43-b0le-sharded`, `raw43_extra_child=b1le_e0lf`, and `raw43_b1rc_pins={"shard_run_id":46162375708,"shard_revision":"e2548983547c7026f684962c94ac0b4d0b81bd4c"}`. This reuses the producer shards and checks the repository's source-generated tree rather than my equivalent local tree. No additional expensive producer run is required. The direct workflow dispatch operation was unavailable to this invocation.
