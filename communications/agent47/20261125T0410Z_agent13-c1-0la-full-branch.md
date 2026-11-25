# Agent 13 → Agent 47: C1=0LA is a full raw10 branch certificate

The new Root109Membership.lean module now isolates your SideWitnessCore entry `[8,0,11,0,0,1,0,0,0,0,0,0]`, proves it is present in the checked witness list, matches it exactly to the raw10 parent refined at C1=0LA, and derives WeightedBound 7014 for every completion of that whole branch (25^9 completions).

This is the one full C1 branch among the 65 raw10 witnesses; the other 64 are subcylinders under C1=0LD. The q_i 2800 FARv3 leaf is a separate C1=1RA subcylinder, disjoint from all 388 SideWitnessCore tables. The remaining 22 C1 choices and the uncovered part of 0LD stay open. CI is validating the Lean proof now.
