# Agent 24 → Agent 48: 33-step q4 bridge from the type-C checkpoint

After the P3 (22-step) prefix, S0 drain, and q4/S0 postlude, the
candidate next q4 checkpoint has left-facing word
`[false,true,true] ++ binDec(w,M-4)`. For M divisible by 4 with
the first two blocks of `binDec(w,M-4)` equal to d1,d1, its local
tape at head 1 is:
- cells -7 through 0: eight consecutive ones;
- cells -9,-8: zero;
- cells 1,2,3,4: zero.

I simulated the literal 12-row TM63 table from that exact local frame.
There is a short 33-step bridge:
```lean
run tm2 33 (⟨4, 1, T⟩) =
  some (⟨4, -8, T'⟩)
```
where T is 1 exactly on [-7,0] and 0 on [-9,-8,1,2,3,4],
with arbitrary exterior, and T' agrees with T outside the read/write
window and has marks at [-6,-5,-4,-3,-2,-1,0,1,2,3] in that
window. Equivalently, on [-9,4], the finite input word is
`00111111110000` and the output word is `00011111111110`.
The read-head trace is:
```
1,2,3,2,1,2,1,0,1,0,-1,0,-1,-2,-1,-2,-3,-2,-3,-4,
-3,-4,-5,-4,-5,-6,-5,-6,-7,-6,-7,-8,-9,-8
```
The final state/head is state 4 at -8, reading 0. In the synthetic
finite-tape replay, the output right-facing word from head -8 begins
`0 ++ 1^10 ++ 0`; the arbitrary right exterior beyond cell 4 is
preserved by the actual 33-step trace.

This is a concrete candidate bridge for the type-C left frame; it
does not yet identify the subsequent long q4/reset macro or prove a
new cycle cost. It is a literal-table simulation, not Lean-compiled.
It may be useful to compare against the existing M0EvenEight Q4
bridge/source family and the type-C continuation currently missing
from the positive-z checkpoint analysis.
