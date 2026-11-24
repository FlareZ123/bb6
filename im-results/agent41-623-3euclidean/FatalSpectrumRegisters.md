# Three-register exact ternary spectrum

The full failure set for the original #623 drain can be encoded as a single
integer M(b), whose bit at a is one iff drainB(a,b,d) fails. The existing
Agent49FullFailureSpectrumSource supplies the all-input recurrence and
original-source connection. Unlike computing a list and repeatedly asking
whether zero belongs to neighboring spectra, a single most-significant-digit
fold computes three consecutive masks simultaneously.

For q use registers (A,B,C) = (M(max(q-1,0)), M(q), M(q+1)), initialized at
q=0 by (0,0,1). Appending ternary digit r replaces them as follows:

| r | new A | new B | new C |
|---|---|---|---|
| 0 | 2B + A mod 2 | floor(A/2) | 2B + 1 |
| 1 | floor(A/2) | 2B + 1 | 2C + B mod 2 |
| 2 | 2B + 1 | 2C + B mod 2 | floor(B/2) |

Proof: the original exact flat recurrence gives the three middle-mask
relations by shifting the mask and inserting the appropriate zero-budget
bit. Apply those same relations at 3q-1 and 3q+3 to obtain the outer
registers. For q=0, the zero masks make the saturated predecessor correct.
This proves the invariant by induction on ternary prefixes; leading zero
digits fix the seed. Each ternary digit requires a bounded number of
integer register operations, rather than recursive membership subqueries.
The mask widths are logarithmic in b; this is an operation-count
improvement, not a claim of linear bit complexity.

FatalSpectrumRegisters.lean contains the parametric all-Nat proof:
masks_correct and masks_append. Both compiled locally in Lean 4.36.0-rc2
with only propext and Quot.sound. FatalSpectrumRegistersSource.lean connects
the theorem to the previously source-accepted badAll equivalence; its
original-source CI acceptance is still pending. No new root orbit closure
or BB(6) bound follows merely from computing the exact failure set.
