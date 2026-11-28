# Raw11 q0-148: source-checked right-moving four-cell glider

**New formal theorem:** `BB6Coverage.Agent31Pump.Raw11Q0RightGlider148.cover : ∀ B, Cover (WeightedBound B) table`, for the exact partial machine

```
1RB1LC_1RC1RA_0LA0LD_1LA0RE_0RF---_1RD0LB
```

Source `Raw11Q0RightGlider148.lean`. Original-source Lean 4.36.0-rc2 CI [run 46091581190](https://github.com/FlareZ123/bb6/actions/runs/46091581190), job 140813485772 **success**, reports exactly `[propext, Classical.choice, Quot.sound]` axioms, with no `sorry` or `native_decide`. Exact parent source-table cut registered in `generate-coarse-parent-shards.cjs`.

The proof is *not* a finite simulation claim. In the source machine (state numbers A=0,...,F=5), at ordinary time **2976** from blank it reaches

```
state C, left head-inclusive tape U ++ Xseed, empty right tape
U = 0111111111111111111100  (22 bits)
Xseed = 100100110010010010010010011001001001  (36 bits)
```

The `Tails.Cert` checker proves **for all arbitrary finite bit strings `X`**,

```
run0 table 226 (C, U++X, []) = some (C, U++1001++X, []).
```

Each finite induction step is a positive 226-step return with the same indefinite suffix, preserving compatibility under any completion of the E1-hole transition. The source `Multi.never_of_region` theorem converts the 2976-step seed and parametric closed region to `NeverHalts` for every completion. The forbidden transition is never read. This is a genuine source-accepted nonhalting proof.

The frozen q0-148 parent search root `1RB1LC_1RC---_0LA0LD_------_------_------` (run [46057416175](https://github.com/FlareZ123/bb6/actions/runs/46057416175), 4,789,377 nodes, 24 exceptional one-hole leaves, cap=0) now has candidate classifications for **23** exceptions: **22** reach their missing transition within 6158 primitive steps, and the glider above is proved infinite. The sole remaining exceptional leaf is

```
1RB1LC_1RC0RE_0LA0LD_1LA0RF_1RB1RD_0RC---
```

Its unspecified F1 transition was not queried during a five-million-step independent blank simulation; **that does not establish nonhalting**. General-purpose radius ≤9 local abstract analyses and simple ngram/run abstractions yielded false-positive paths to F1, hence do not decide it. A targeted regular-language source-certificate search has been submitted via `find-hard-leaf-far.cjs`; do not claim a complete parent Cover until this leaf and the full source tree are kernel checked. `search-one-sided-gliders.cjs` and `generate-one-sided-glider-lean.cjs` now generalize the discovery/Lean-emission method to other partial machines.

All findings here are either explicitly original-source proved (the single glider) or clearly labeled computational; a universal BB(6) upper bound remains open.
