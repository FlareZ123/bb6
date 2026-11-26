# Raw10 refined residual: source-accepted inclusion consumer (30 / conditional 28 boxes)

## Mathematical interface and evidence

A source-indexed closed rectangle continues to bound every refined subrectangle, even when extra certified cylinders fragment it. For finite complete slot enumeration S, if each allowed set of r is included in the corresponding allowed set of c, then Fits r m implies Fits c m. `RectCover.lean` proves this and the generic explicit-complement consumer in Lean 4.36.0-rc2. Both exported theorem axiom profiles are exactly [`propext`, `Quot.sound`].

The exact Raw10 adapter `Raw10RefinedCut.lean` uses the existing source remainder constructor, the same 65 side witnesses, held leaf, fixed cycle and two-move halt cylinders as the expanded 41-box interface, and source box bounds for 8 and 18–24. It deliberately has no dependency on the old canonical77/78 roster or legacy generated import chain. The source closure, including `Raw10RefinedCut.lean`, `Raw10RefinedHeld.lean`, `Raw10RefinedBox5.lean`, and `Raw10RefinedBox7.lean`, was accepted in [run 45892933847](https://github.com/FlareZ123/bb6/actions/runs/45892933847). The Box5/7 source closure is now preserved as artifact `raw10-box5-box7-source-closure` from [run 45896143748](https://github.com/FlareZ123/bb6/actions/runs/45896143748) (121,164,690 bytes; SHA-256 `5f6a27b9fb68627e077a6168fe82609eea07cccba437559da6e6df7454ef383d`). The held-leaf premise remains explicit, and the 16/17 bounds remain explicit premises.

Independent executable combinatorics (`replay.cjs`, run from any directory with Node.js) on the actual 66 encoded source rows gives:

| Original rectangle | Refined index (zero-based) | Mass |
|---|---:|---:|
| 8 | 15 | 575 |
| 16 | 23 | 3,515,625 |
| 17 | 24 | 146,250 |
| 18–24 | 25–31 | 52,500 |

The seven 18–24 boxes and the remainder of original box8 remove 53,075 completions from the 41-box partition, leaving 33 explicit boxes. The source-accepted original-source Covers for base34 boxes5 and7 remove two further exact members: kernel-checked `open31` proves that 31 refined rectangles remain, while `open29` proves 29 when the separate original-source box16 and box17 bounds are supplied.

Original base34 box6 is now also source-accepted with weighted bound 75. The exact probe in [run 45898296738](https://github.com/FlareZ123/bb6/actions/runs/45898296738) confirms that adding `raw10Remainder[6]!` to the accepted box5/7/8/18–24 cut leaves **30 open rectangles**, and the candidate with separate box16/17 bounds leaves **28**. These counts were evaluated by Lean against the actual finite lists. The source consumer exposes `box6_weighted` for `Agent49Box6.baseBox`; the new adapter `Raw10RefinedBox6.lean` proves the base-box/index equality by `decide`, transfers the bound, and builds the 30/28 conditional parent Covers. Compilation and axiom audits are running in [run 45899419790](https://github.com/FlareZ123/bb6/actions/runs/45899419790). Treat the wrapper theorems as pending until that run succeeds.

## Remaining gates and next cut

- The new `parentCover30` requires a bound for each of the 30 retained refined rectangles and the explicit held-leaf premise. `parentCover28` additionally requires the separate box16 and box17 bounds, but still leaves 28 explicit rectangles. Neither theorem closes the parent by itself.
- The source-accepted Box6 artifact is `raw10-box6-source-closure`, from run 45898296738 (209,883,455 bytes; SHA-256 `7074af84540abfd6689c90386d4ef882649269f5b662ae10c6809d1be0c963df`). Its thin consumer reused 127 Box5/7 modules, compiled a 164-module probe closure, and compared all 94 shared modules with zero identity mismatches and zero provenance differences.
- Agent13 owns the separate box16/17 source integrations. Do not duplicate that work; the 28-open candidate still requires those explicit bounds.
- The held-leaf premise remains explicit.
- Exact membership of the B0=1LC parent in the current Canonical64/Canonical58 roster is being checked in [run 45898953769](https://github.com/FlareZ123/bb6/actions/runs/45898953769). Even if membership is confirmed, a full parent Cover remains outstanding. BB(6) remains open.
