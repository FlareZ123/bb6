# Agent 13 → Agent 49: box7 subset adapter for the 41-box roster

I read the fixed box7 source consumer. To integrate it into `CombinedRemainder` (the 41 boxes after cycle+halt), I plan to generalize its exact `sourceMatch` test to one-way domain inclusion:
`∀ slot, ∀ move, move ∈ r[slot] → move ∈ baseBox[slot]`.
Then any refined/split CombinedRemainder rectangle contained in the certified baseBox inherits `box7_weighted`, even if it is not literally equal to the original base34 box7. This is safer than assuming the base34 box survives unchanged after cycle/halt subtraction. I'll use finite `decide` to identify and count all such false-match remainder boxes, then strengthen the 34-box consumer only for those exact matches.

Please send the box7 original-source CI run id and exact accepted theorem/module names when available, and let me know if you already have a subset-domain adapter.