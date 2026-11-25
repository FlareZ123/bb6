# Raw85: three exact nonhalting sweep certificates (Agent 40)

Three leaves of raw85 / F1=1RA previously reported as no-hit by finite automata search admit simple inductive block sweeps. The established generator `../agent31-three-hole-tnf/generate_sweeps.py` now includes them as M10–M12. Its `SweepPumping.lean` semantics quantifies over **every compatible completion**. The unassigned transition is never queried in these infinite executions.

| Partial table | Entry (raw moves) | State and left zipper, right empty | Positive return cost |
|---|---:|---|---|
| `1RB0LE_1RC1LF_0RD1RF_1LD1RE_---0LB_0RC1RA` | 26 | D: `00010 (101010)^n 1010` | 93+36n |
| `1RB0LE_1RC1LF_0RD---_1LD1RE_1RA0LB_0RF1RA` | 32 | E: `0 (10111011)^n 101110` | 113+76n |
| `1RB0RD_1RC1LF_0RD1RF_1LD1RE_---0LB_1RC1RA` | 1 | B: `0 (11111)^n 1` | 20+44n |

Left zipper lists the scanned symbol first, then cells to its left; missing symbols are blank. Each return sends n to n+1. The exact phase decompositions are respectively:

- 21 + 30n + 43 + 6n + 29
- 4 + 28n + 38 + 48n + 71
- 2 + 35n + 13 + 9n + 5

Each n-dependent phase uses a one-block literal reduction quantified over arbitrary untouched tails and the existing sweep induction. A local Lean 4.36.0-rc2 check of all three entry, phase and growth theorems against a literal copy of the executable zipper definitions and sweep lemmas succeeded; each growth theorem depends only on propext and Quot.sound. The actual original-source nonhalting proof closure still requires CI.

Reproduce with `python im-results/agent31-three-hole-tnf/generate_sweeps.py` and existing source closure compiler on generated SweepData.lean. The sibling generator automatically maps TABLES to exact partial table keys; no candidate FAR mask or new special case is necessary. The raw85 parent workflow still must check all other branches and its bound before removing that cylinder from the frontier.
