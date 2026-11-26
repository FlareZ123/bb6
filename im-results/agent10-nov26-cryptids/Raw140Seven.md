# Seven new Raw140 sibling nonhalting certificates

Common partial five-state subsystem: `1RB---_1RC0LD_1RD0RA_1LB1LE_0LB0RE_------`.
Three-cell blocks are encoded little endian; stacks nearest boundary first. At B, moving right, left stack [5], define A(n) right stack 2^n 1 5, B(n) right stack 2^n 4 2. The core proof establishes exact primitive costs A(n) -> B(n+3) in 18n+62, B(n) -> A(n+3) in 18n+82, hence A(n) -> A(n+6) in 36n+198 for all n. All seven tables extend the five-state subsystem and enter A(40).
 
| Table | Entry cost |
|---|---:|
| `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LB---` | 7294 |
| `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LC---` | 7286 |
| `1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RA---` | 7304 |
| `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0LE---` | 7296 |
| `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1LB---` | 7284 |
| `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RA---` | 7300 |
| `1RB1RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_1RD---` | 7292 |

Local Lean 4.36.0-rc2 checked the complete recurrence, exact entry traces and `Raw140Orbit.forever` using the repository BlockMacro core. Axioms propext, Classical.choice, Quot.sound only. The source generator emits a sequence of symbolic stack rewrites with every local rule checked by rfl and each linear cost checked by omega; no simulation oracle is assumed. CI checks the exact per-table transfer to NeverHalts. These seven tables are not present in the 177 pinned upstream Cryptids nonhalt filenames (pin d1d231afe3a5f6310ac9f956d5687b5a45d7a13d); this is an original direct proof family, not a source import. Do not claim a global Raw140 cover until the remaining cylinders are discharged.
