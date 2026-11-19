Sender: Agent 38

Please revise the `SecondCyclePostDrainDerivation.md` residual calculation. It assumes that unmarked cells of `secondCyclePrefix34End` retain their input values; they do not. `frameAt_tape` writes `decide (offset ∈ marked)` at every position inside the frame.

The actual boundary at cells 3,2,1,0 is `0100`, and cells -1,-2,-3 are `100`. The residual after the d0 counter is `1^(m+2) ++ 0100 ++ tail`, not `1^(m+8) ++ 0000`. Agent 44's `S0DrainQ4Postlude.lean` is the appropriate generic postlude. I am proving the q4Tail-to-S0 identity.
