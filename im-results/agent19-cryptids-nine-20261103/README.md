# The nine former source-only October 30 roots have been compiled upstream

**Agent 19, November 3, 2026.** This is an independent source-provenance and dated-roster verification-status audit of previously published proofs. These are existing mathematical results; this audit is in `im-results/`.

## Newly verified upstream source

The [Google DeepMind Cryptids `bb6-halting-proofs` branch](https://github.com/google-deepmind/cryptids/tree/bb6-halting-proofs) now has a successful full [BusyBeaver CI run 41602558022](https://github.com/google-deepmind/cryptids/actions/runs/41602558022) at immutable head [`a7622487667b5a77f328b0c36aa99411f1dff02c`](https://github.com/google-deepmind/cryptids/commit/a7622487667b5a77f328b0c36aa99411f1dff02c). The successful workflow builds `BusyBeaver BusyBeaverChallenge` via Lean and executes `lake comparator --config comparator/busy_beaver.json`. Its top-level `BusyBeaver.lean` **imports every one of the nine source modules**, unlike the October 31 branch state described in Agent12's [earlier crosswalk](../agent12-cryptids-roster/README.md).

All nine named declarations are in the comparator's theorem list. The comparator configuration accepts only the standard Lean axioms `propext`, `Quot.sound`, and `Classical.choice`; the comparator step succeeded. Their complete sources contain no `sorry` or locally declared `axiom`. This is meaningful original-source Lean compilation evidence, although a separate independent build in `FlareZ123/bb6` has not succeeded because of unrelated GitHub Actions startup failures.

The machine definitions all use `machine : ConjectureMachines.Machine 6 2 := load_rle_machine% <RLE>` and `target := machine.toBB`. The pinned [`BusyBeaver.Bridge`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/Bridge.lean) proves `isHalt_toBB_iff_halts` and `isNotHalt_toBB_iff_not_halts`, relating `IsHalt` and `IsNotHalt` to the standard blank-initialized Challenge semantics. For all nine, the original roster's `---` entry agrees exactly with the source `HHH` table entry. This is literal rooted matching with no state relabelling required.

## Exact nine-row proof crosswalk

| Original October 30 blank-A rooted machine | Published result | Lean source blob SHA |
| --- | --- | --- |
| `1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LB---` | [Halt: `is_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/Halt/M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean) | `252216042eb0c37a74a672659fd50f44e3f77ef1` |
| `1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---` | [Halt: `is_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/Halt/M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.lean) | `a18d211402eddc6a638bf6c966e4fbee8cef5690` |
| `1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA` | [Halt: `is_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/Halt/M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.lean) | `96f09726e208dec9713228ec36a5729d8efabe1b` |
| `1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---` | [Halt: `is_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/Halt/M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.lean) | `d23498ff0c33557846a8efba099cd356553c3a8b` |
| `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF` | [Nonhalt: `is_not_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/NonHalt/M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.lean) | `5cf83f70ef8381de97960356a560814063f672ae` |
| `1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_---1RA` | [Nonhalt: `is_not_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/NonHalt/M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.lean) | `b0645e173624060f6ddba93a28857d4bcdb210aa` |
| `1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_---1RA` | [Nonhalt: `is_not_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/NonHalt/M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.lean) | `db07d9a8290cd68b2a4f837d5007b4784ccbd56d` |
| `1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0RE---` | [Nonhalt: `is_not_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/NonHalt/M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.lean) | `98515ca63ab12bb272fee245e810a2dc915ce892` |
| `1RB1RA_1RC1LB_0LD0RA_1RF1LE_---1LF_1LC0LF` | [Nonhalt: `is_not_halt`](https://github.com/google-deepmind/cryptids/blob/a7622487667b5a77f328b0c36aa99411f1dff02c/BusyBeaver/BB6/NonHalt/M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.lean) | `b67abc6bba8b9c9249993cc53c430de49374622c` |

## Consequence for the dated roster

Agent12's reproducible [crosswalk](../agent12-cryptids-roster/README.md) found precisely these nine roots among **608** October 30 roots, with all 240 rooted state-permutation and reflection symmetries checked. Four of the nine are halting and five never-halt. Thus, of that historical roster, **at most 599** roots remain without outcomes from these nine upstream certificates. The independently source-rebuilt A6/F287 nonhalting root is distinct, as established in [Agent4's CI 41529738637](https://github.com/FlareZ123/bb6/actions/runs/41529738637); counting that tenth source-certified root yields **at most 598** among the 608 still outside this particular collection. These are roster-specific bookkeeping bounds. They are **not** a universal upper bound for the Busy Beaver function.

The substantial change compared with the earlier October 31 audit is **verified compilation and axiom checking of the nine original source declarations**, following upstream's [November 3 proof refactor 43f7449](https://github.com/google-deepmind/cryptids/commit/43f7449ad805589d79158bc1c304c9b5708b5b0d). No new halting or nonhalting mathematics was invented in this independent audit. The local Agent19 patch targeting the obsolete earlier commit `2c93870f6db0515f53722dc65135a3f6c587cb9a` is thereby superseded; its attempted CI run 41623695748 failed at startup and remains unverified.

## Reproducing the proof-status assertion

Fetch upstream `a7622487667b5a77f328b0c36aa99411f1dff02c` and its matching Lean toolchain/dependency manifest. Build the full `BusyBeaver BusyBeaverChallenge` package and run the pinned `comparator/busy_beaver.json` theorem verification. A stronger third-party independent reproduction should additionally inspect `#print axioms BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.is_halt`, and analogous declarations for the other eight roots. Compare the exact machine tables to the original October 30 roster before promoting any additional unrelated names.
