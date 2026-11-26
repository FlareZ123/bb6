# Raw10 refined residual: source-accepted inclusion consumer (31 / conditional 29 boxes)

## Mathematical interface and evidence

A source-indexed closed rectangle continues to bound every refined subrectangle, even when extra certified cylinders fragment it. For finite complete slot enumeration S, if each allowed set of r is included in the corresponding allowed set of c, then Fits r m implies Fits c m. RectCover.lean proves this and the generic explicit-complement consumer in Lean 4.36.0-rc2 (local compiler b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). Both exported theorem axiom profiles are exactly [propext, Quot.sound].

The exact Raw10 adapter `Raw10RefinedCut.lean` uses the existing source remainder constructor, the same 65 side witnesses, held leaf, fixed cycle and two-move halt cylinders as the expanded 41-box interface, and source box bounds for 8 and 18–24. It deliberately has no dependency on the old canonical77/78 roster or legacy generated import chain. The full source closure, including `Raw10RefinedCut.lean`, `Raw10RefinedHeld.lean`, `Raw10RefinedBox5.lean`, and `Raw10RefinedBox7.lean`, is accepted in [run 45892933847](https://github.com/FlareZ123/bb6/actions/runs/45892933847), which compiled 127 project modules. The held-leaf premise remains explicit, and the 16/17 bounds remain explicit premises.

Independent executable combinatorics (replay.cjs, run from any directory with Node.js) on the actual 66 encoded source rows gives:

| Original rectangle | Refined index (zero-based) | Mass |
|---|---:|---:|
| 8 | 15 | 575 |
| 16 | 23 | 3,515,625 |
| 17 | 24 | 146,250 |
| 18–24 | 25–31 | 52,500 |

The seven 18–24 boxes and the remainder of original box8 remove 53,075 completions from the 41-box partition, leaving 33 explicit boxes. The newly accepted original-source Covers for base34 boxes5 and7 remove two further exact members: kernel-checked `open31` proves that **31 refined rectangles remain**, while `open29` proves 29 when the separate original-source box16 and box17 bounds are supplied. Both count theorems and the conditional parent adapters compiled in run 45892933847 with standard axioms. A separate source-accepted box6 Cover (run 45893206793; bound 75 over 375,000 completions) is not yet consumed by this refined adapter. These are exact local parent-cut counts, not a completed Raw10 parent Cover or a global roster reduction.

## Remaining gates and next cut

- `parentCover31` still requires a bound for each of the 31 retained refined rectangles and the explicit held-leaf premise. `parentCover29` additionally requires the box16 and box17 bounds, but still leaves 29 explicit rectangles. Neither theorem closes the parent by itself.
- Original base34 box6 is now independently source-accepted: `BB6.Agent49Box6.raw10_box6_closed` and `residual_without_box6`, run 45893206793, weighted bound 75. It has not yet been added to `Raw10RefinedCut.accepted`. The next concrete reduction is to prove that every refined rectangle matched by the box6 source cylinder is covered by that exact source rectangle, add its weighted bound 75, and kernel-check the new open-box count. Do not infer the count from the original box index; compute it from the exact `RectCover.covered` relation.
- Agent13 owns the separate box16/17 source integrations. The held-leaf premise remains explicit.
- The B0=1LC parent is not yet consumed by Canonical58: exact membership in the current Canonical64/Canonical58 roster and a full parent Cover remain outstanding. BB(6) remains open.
