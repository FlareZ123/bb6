# Five 1LE leaves: shared unbounded base-four counter

The theorem `BB6.Agent11Raw391LEBinaryFive.never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m` is locally kernel-checked under Lean 4.36.0-rc2 with axioms propext and Quot.sound only. Variant mapping in the exact normalized-open list:

| Variant | Leaf index | Partial table |
|---|---:|---|
| a | 19021 | 1RB1LE1RC1RE0RD---1LD0RA1LF1RB0RA0LF |
| b | 19049 | 1RB1LE1RC1RE0RD---1LD0RA1LF1RB0RE0LF |
| c | 19091 | 1RB1LE1RC1RE0RD---1LD0RA1LF1RB1LC0LF |
| d | 20727 | 1RB1LE1RC0RE0RD---1LD0RA1LF0RB0LF1RB |
| e | 20938 | 1RB1LE1RC0RE0RD---1LD0RA1LF0RB0LF1RE |

The word W is encoded little-endian by four-cell digits 0000,1000,0111,1111, followed by [] or [1]. E scans a run of maximal digits, transferring each into four identical filler cells on the left. A nonmaximal digit increments; F transfers the filler cells back as zero digits and restores the finite frame. Empty suffix changes to [1], and [1] changes to 0111, extending the counter. The finite frame and fill bit differ by variant, but the scan and reset theorems are shared. Each macro has positive length, including the carry step; the inductive invariant proves arbitrarily long live runs and hence NeverHalts, without an assumption on any maximum tape width. This resolves five of the 49 previously unclassified 1LE leaves. The 1LE parent itself remains unproved.

Source: [Raw391LEBinaryFive.lean](Raw391LEBinaryFive.lean). Local compilation used the already accepted SweepPumping dependency artifact.
