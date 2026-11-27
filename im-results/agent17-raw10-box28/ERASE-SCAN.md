# Erasing-rewind one-marker invariant

The earlier zero-gap scan recurrence admits a stronger, shorter one-step invariant, which permits several additional transitions through D. It has no restriction on the farther-left tape and no simulation cutoff.

Fix A0=1RB, B0=1LC, C1=0LD, D0=0RE, D1=0LD. A1, B1, C0 are arbitrary. E0/F0 independently allow seven moves: right to D,E,F with either write bit, or 0LD. E1/F1 independently allow eleven moves: right to A,D,E,F with either write bit, 1RB, or left to D with either write bit. Thus 7²·11²·25³ = 92,640,625 distinct labeled complete tables; imposing Box28's C0=1LC gives 3,705,625. These are disjoint from the D1=1LD reset scan family. Counts describe the explicit slot choices, not distinct TNF classes or global roster subtraction.

## Inductive invariant

Call a right stream sparse if it has at most one 1. The blank stream, a single leading 1 followed by blank, and any zero prefix of a sparse stream are sparse.

| State | Invariant |
|---|---|
| A | current symbol zero, right stream blank |
| B | current symbol zero, right stream blank, nearest-left symbol one |
| C | current symbol one, right stream sparse |
| D | right stream sparse, current symbol arbitrary |
| E/F | current symbol followed by right stream sparse |

No other left tape property is needed. At A0 the B condition holds; at B0 the C condition holds because B writes a new marker. At C1 and D1 a zero is prepended to the right stream; at D0 the rightward scan continues into a sparse suffix. An E/F zero right move can enter D/E/F, or a zero-writing left move to D prepends a zero. An E/F one has blank right suffix, hence all listed marker moves preserve the target state's invariant. In particular the 1RB move installs the required nearest-left one. The invariant is true at the blank start and inductive under every permitted step. Arbitrary A1, B1 and C0 functions are never called.

`Box28EraseScan.lean` replaces the narrower zero-gap macro with this invariant. The exact stream model was checked locally in Lean 4.36.0-rc2 with verbatim dependency definitions and standard axioms [propext, Quot.sound]. Original-source transport in `Box28EraseScanSource.lean` is pending full audit. The earlier 4²·7²·25³ family is a strict subset; do not double-count it.
