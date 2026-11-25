# Raw10 base box 8: 600-completion halt slice

**Status:** intermediate computational decomposition; not yet a Lean proof of the whole box.

## Exact box

The ranked singleton-projection search identifies base box 8 as

```text
1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_------
```

Its domain sizes are `[1,1,1,1,1,1,1,1,1,1,24,25]`, hence exactly 600 completions. The final two slots are F0 (24 ordinary moves) and F1 (25 choices, including halt).

## Structural partition

- **576 completions:** F1 is an ordinary transition. All 12 transitions are then defined, so these machines cannot halt under the standard two-symbol convention. This part is structurally nonhalting, not a simulation claim.
- **24 completions:** F1 is the undefined/halting transition. Only F0 varies.

For the 24 F1-halt cases, direct blank-tape simulation gives:

| F0 code | F0 move | Outcome |
|---:|---|---|
| 12 | 1RC | halts after 32 steps |
| 22 | 0RF | halts after 11 steps |
| 24 | 1RF | halts after 11 steps |
| 10 | 0RC | exact cycle: starts at step 24, period 14 |
| 1–9, 11, 13–21, 23 | see list below | no halt or exact configuration cycle through 1,000,000 steps |

The 0RC cycle is already represented by the broader 625-completion lasso cylinder in `Raw10Box8Cycle.lean`: its table leaves B1 and F1 unassigned and fixes F0=0RC. The three halting completions are safely below the target score 7014, but are not covered by the separate A1/C1 forced-halt cylinder in `Raw10Box0Halt.lean`; they need individual finite-halting leaves or an equivalent composition.

The remaining 20 F0 choices are:

`1:0LA, 2:0RA, 3:1LA, 4:1RA, 5:0LB, 6:0RB, 7:1LB, 8:1RB, 9:0LC, 11:1LC, 13:0LD, 14:0RD, 15:1LD, 16:1RD, 17:0LE, 18:0RE, 19:1LE, 20:1RE, 21:0LF, 23:1LF`.

All 20 survived one million simulated steps. This is empirical evidence only; it does not prove nonhalting. Their behavior is nevertheless highly structured: several show linear head drift and tape growth, while a few have bounded head range with a growing tape pattern.

## Next computation

`search_box8_halt_slice.py` reproduces the simulation and runs the existing BlockFAR generator separately on each of the 20 unresolved complete tables. Successful outputs are renamed into unique Lean namespaces under the output directory. Manual workflow target: `weighted-tnf-raw10-box8-halt-slice`.

A successful generated certificate proves nonhalting for that individual table. Generator failures are retained as diagnostic outcomes, not treated as evidence of halting or safety. The final Lean composition still needs:
1. a generic lemma for the 576 fully defined completions;
2. finite-halting proofs for the three short halters;
3. the existing F0=0RC lasso;
4. source-accepted nonhalting certificates or stronger invariants for the 20 remaining cases;
5. a finite coverage theorem showing these slices exhaust box 8.

