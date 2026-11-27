# Erasing-rewind scan family

The disjoint D1=0LD variant admits an unconditional invariant with three arbitrary slots. No enumeration of unbounded tape lengths is needed.

Fix A0=1RB, B0=1LC, C1=0LD, D0=0RE, D1=0LD. A1, B1, C0 are arbitrary. E0 and F0 are arbitrary right moves to E or F (either write bit); E1 and F1 are arbitrary right moves to A, E or F (either write bit), or 1RB. Each scanner zero slot has four choices and each marker slot seven choices. Hence 4²·7²·25³ = 12,250,000 distinct complete tables in the ambient labeled table space; with C0=1LC as in Box28, 490,000 tables remain. These are disjoint from the non-erasing D1=1LD scan family.

After four live moves the blank execution has state E and right stream 01 followed by zeros. At every root the right stream is 0^(n+1)1 followed by zeros, and the left starts with zero followed by an arbitrary frame. Scan the zero gap using only E0/F0. Every right write either appends a one to the trailing run of written ones or resets that run by introducing a zero. On the marker:
- a right move to E/F produces infinite drift on the remaining zeros;
- a right move to A reaches blank A, then A0/B0/C1 turns to D and produces a fresh 01 suffix;
- a 1RB move reaches blank B with the freshly written one on its left, so B0/C1 performs the same turn.

In the returning cases the left stream at D has a finite run of ones followed by a zero, with arbitrary farther-left tape. D1 erases each of those ones and D0 moves right from the boundary zero. This restores the root with a new zero gap and one marker. Every macro takes positive time. Neither A1, B1 nor C0 is queried.

`Box28EraseScan.lean` proves the invariant and all-time nonhalting for arbitrary functions at the three gates, locally kernel-checked in Lean 4.36.0-rc2 with the verbatim stream definitions and only propext and Quot.sound. `Box28EraseScanSource.lean` is the original-source transport candidate. Its full source audit is required before use as a certified cut. Counts are derived by the explicit disjoint table-slot choices, not by a global roster claim.
