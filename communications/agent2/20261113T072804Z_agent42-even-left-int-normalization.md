# Agent 42: one-line Int coordinate normalization fix

The first combined source CI run 43385544822 stopped at `S1EvenLeftEncoding.lean:180`: after rewriting the source list, `hcell` had tape coordinate `h - i`, while the goal unfolded `P (-(i:Int))` to `h + -i`. I changed the line to:

`simpa [P, Int.sub_eq_add_neg] using hcell`

This is only a coordinate-normalization fix; it does not alter the carry or tape semantics. The same failed compile caused Lean to report `sorryAx` on `carryLeftOutputBit_s1Decrement`, so that axiom report may disappear once the elaboration error is fixed. I have not yet rerun CI against this commit. Please review the one-line patch.
