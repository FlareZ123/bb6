# q0 open-root audit — 2026-11-26

**Status: candidate-search output, not a nonhalting proof.** The scan ran `coarse-pair.cjs` with open leaves retained for q0 active roots 26, 28, 33, 34, 39, 44, 46, 48, 49, and 51. Full tables and multiplicities are in [`q0-open-root-scan-2026-11-26.json`](q0-open-root-scan-2026-11-26.json).

| q0 active index | tree nodes | open leaves | bound (= max halt + 6) | distinct open tables |
|---:|---:|---:|---:|---:|
| 26 | 361 | 13 | 200 | 13 |
| 28 | 289 | 1 | 63 | 1 |
| 33 | 985 | 1 | 162 | 1 |
| 34 | 1777 | 4 | 81 | 4 |
| 39 | 1873 | 16 | 144 | 16 |
| 44 | 2041 | 5 | 90 | 5 |
| 46 | 2017 | 1 | 64 | 1 |
| 48 | 3745 | 2 | 151 | 2 |
| 49 | 5785 | 21 | 234 | 21 |
| 51 | 4393 | 31 | 208 | 31 |

## Root 26 correction

The root26 search tree has **13 open leaves and 13 distinct open tables**, not one. The first proposed `solid26_tm` is only one of these residual leaves. All 13 residual tables leave F0 undefined, but they vary in E0 and/or F1:

1. `1RB1RD1RC0RE0LA0RF1LA1LD1LE0LA---1LA` (multiplicity 1)
2. `1RB1RD1RC0RE0LA0RF1LA1LD1RA0LA---0RD` (multiplicity 1)
3. `1RB1RD1RC0RE0LA0RF1LA1LD0LB0LA---0RD` (multiplicity 1)
4. `1RB1RD1RC0RE0LA0RF1LA1LD1RB0LA---0RD` (multiplicity 1)
5. `1RB1RD1RC0RE0LA0RF1LA1LD0LC0LA---0RD` (multiplicity 1)
6. `1RB1RD1RC0RE0LA0RF1LA1LD0RC0LA---0RD` (multiplicity 1)
7. `1RB1RD1RC0RE0LA0RF1LA1LD1LC0LA---0RD` (multiplicity 1)
8. `1RB1RD1RC0RE0LA0RF1LA1LD0LD0LA---0RD` (multiplicity 1)
9. `1RB1RD1RC0RE0LA0RF1LA1LD1LD0LA---0RD` (multiplicity 1)
10. `1RB1RD1RC0RE0LA0RF1LA1LD0LE0LA---0RD` (multiplicity 1)
11. `1RB1RD1RC0RE0LA0RF1LA1LD1RA0LA---0RE` (multiplicity 1)
12. `1RB1RD1RC0RE0LA0RF1LA1LD1LD0LA---0RE` (multiplicity 1)
13. `1RB1RD1RC0RE0LA0RF1LA1LD1LE0LA---0RE` (multiplicity 1)

Consequently, the current `q0-row26.cjs` single-solid generator is invalid for closing the whole parent root. The proposed single nonhalting cylinder does not discharge the other 12 leaves. Root 26 is excluded from the current integration target until every distinct residual is proved safe or a genuinely general theorem covers the family.

## Root 28

Root28 has 1 open leaf and 1 distinct open table:
`1RB1RD1RC0RE0LA1RF1LA1LD1LE0LA---0RE`.

This matches the proposed row28 partial machine. Its source-level sweep proof and exact q0 consumer are included in integrated run `45766737173`. The standalone run `45764648102` was cancelled after 20 minutes in the compile step to avoid duplicating the integrated audit.

## Other promising roots

- Root 33: one open leaf, missing C1.
- Root 46: one open leaf, missing F0.
- Root 48: two open leaves.
- Roots 34 and 44: four and five open leaves.
- Roots 39, 49, and 51: 16, 21, and 31 open leaves.

For roots 33 and 46, separate 1,000,000-step simulations did not reach the respective missing transitions. The observed local implications were:
- Root 33: B0 always had a zero immediately to its right (4,000 observations); F1 always had a zero immediately to its left (3,911 observations).
- Root 46: C1 always had a one immediately to its right (99,540 observations).

A finite-radius abstraction that forgets the tape outside a window around the head still admits abstract paths to the missing transition for radii 1 through 6. A proof likely needs a global regular-language/tape-shape invariant or an explicit macro-family.

The Node-only scan completed successfully in CI run `45766350968`. None of the simulation or scan observations here is an infinite-run proof.
