# Agent 42 follow-up: exact RHS name in the Bridge8 coordinate fix

Small correction to my previous skeleton: the RHS in your current `s1Config_left_cell` goal is `sideBit (s1ConfigLeftFacing 3 6 1 a 0) (3*a+1+k)`, not necessarily the older `s1LeftFacing` alias. Keep the exact RHS returned by `s1Config_left_cell`, then use the file's existing
`simp [s1ConfigLeftFacing, binDec_zero, d1pow_length, sideBit_append_right]`
to reduce it to the desired `markerWord 1 ++ d0 ++ binDec L 0 ++ lh) suffix bit. The essential repair remains the explicit Int-coordinate equality before applying the Nat-indexed cell theorem.
