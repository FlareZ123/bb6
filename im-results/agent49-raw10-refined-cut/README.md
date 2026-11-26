# Raw10 refined residual: source-accepted inclusion consumer (30 / conditional 28 boxes)

## Mathematical interface and evidence

A source-indexed closed rectangle continues to bound every refined subrectangle, even when extra certified cylinders fragment it. For finite complete slot enumeration S, if each allowed set of r is included in the corresponding allowed set of c, then Fits r m implies Fits c m. `RectCover.lean` proves this and the generic explicit-complement consumer in Lean 4.36.0-rc2. Both exported theorem axiom profiles are exactly [`propext`, `Quot.sound`].

The exact Raw10 adapter `Raw10RefinedCut.lean` uses the existing source remainder constructor, the same 65 side witnesses, held leaf, fixed cycle and two-move halt cylinders as the expanded 41-box interface, and source box bounds for 8 and 18–24. It deliberately has no dependency on the old canonical77/78 roster or legacy generated import chain. The source closure, including `Raw10RefinedCut.lean`, `Raw10RefinedHeld.lean`, `Raw10RefinedBox5.lean`, and `Raw10RefinedBox7.lean`, was accepted in [run 45892933847](https://github.com/FlareZ123/bb6/actions/runs/45892933847). The Box5/7 source closure is preserved as artifact `raw10-box5-box7-source-closure` from [run 45896143748](https://github.com/FlareZ123/bb6/actions/runs/45896143748) (121,164,690 bytes; SHA-256 `5f6a27b9fb68627e077a6168fe82609eea07cccba437559da6e6df7454ef383d`). The source-accepted held-leaf certificate is supplied internally by `Raw10RefinedHeld.held_weighted`; only the open-rectangle bounds and the optional box16/17 bounds remain external premises.

Independent executable combinatorics (`replay.cjs`, run from any directory with Node.js) on the actual 66 encoded source rows gives:

| Original rectangle | Refined index (zero-based) | Mass |
|---|---:|---:|
| 8 | 15 | 575 |
| 16 | 23 | 3,515,625 |
| 17 | 24 | 146,250 |
| 18–24 | 25–31 | 52,500 |

The seven 18–24 boxes and the remainder of original box8 remove 53,075 completions from the 41-box partition, leaving 33 explicit boxes. The source-accepted original-source Covers for base34 boxes5 and7 remove two further exact members: kernel-checked `open31` proves that 31 refined rectangles remain, while `open29` proves 29 when the separate original-source box16 and box17 bounds are supplied.

Original base34 box6 is source-accepted with weighted bound 75. The exact probe in [run 45898296738](https://github.com/FlareZ123/bb6/actions/runs/45898296738) confirms that adding `raw10Remainder[6]!` to the accepted box5/7/8/18–24 cut leaves **30 open rectangles**, and the candidate with separate box16/17 bounds leaves **28**. These counts were evaluated by Lean against the actual finite lists.

The refined adapter `Raw10RefinedBox6.lean` is now kernel-checked in [run 45906154912](https://github.com/FlareZ123/bb6/actions/runs/45906154912). It proves `BB6.Agent49Box6.sourceMatch raw10Remainder[6]! = true` and transfers `box6_weighted` through `sourceMatch_sound`; this correctly avoids attempting decidable equality of function-valued rectangles. The run audited `parentCover30` and `parentCover28` and uploaded `raw10-box6-refined-parent-cut` (artifact ID `15158192432`, 209,984,510 bytes, SHA-256 `783b0daa58f8d42e6bc49bb29b6cb743b70acc6070337faa2686aa02379c55e9`). The 30/28 theorems are conditional only on the stated open-rectangle bounds (and, for 28, the separate box16/17 bounds). The held-leaf obligation is already discharged internally; neither theorem closes the parent by itself.

## Remaining gates and next cut

- The new `parentCover30` requires a bound for each of the 30 retained refined rectangles; it supplies the held-leaf proof internally. `parentCover28` additionally requires the separate box16 and box17 bounds, but still leaves 28 explicit rectangles. Neither theorem closes the parent by itself.
- The source-accepted Box6 artifact is `raw10-box6-source-closure`, from run 45898296738 (209,883,455 bytes; SHA-256 `7074af84540abfd6689c90386d4ef882649269f5b662ae10c6809d1be0c963df`). Its thin consumer reused 127 Box5/7 modules, compiled a 164-module probe closure, and compared all 94 shared modules with zero identity mismatches and zero provenance differences.
- Agent13 owns the separate box16/17 source integrations. Do not duplicate that work; the 28-open candidate still requires those explicit bounds.
- The held-leaf obligation is discharged by `Raw10RefinedHeld.held_weighted`, which uses the source-accepted `BB6BlockFAR.Held.never` certificate.
- Exact membership of the B0=1LC parent in the accepted Canonical58 roster is now kernel-checked in [run 45908318915](https://github.com/FlareZ123/bb6/actions/runs/45908318915). The probe verifies `p10_count59 = 1`, `p10_not_removed`, and `p10_count58 = 1`; the parent is therefore one of the 58 global residuals. Artifact `raw10-canonical58-membership-probe` is ID `15158737930` (56,216 bytes; SHA-256 `b44e68e78c6c29440a597cc54e6edc5cd0d53cbe026ee9717c753a834e6fd6ec`). The proof uses the source-pinned Canonical59 artifact and the exact B0=1LC and Raw113 source definitions. Closing this parent would reduce the global residual count to 57, but its full Cover remains outstanding. BB(6) remains open.
