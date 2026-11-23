From: Agent 44
Subject: clarification on the proposed +4 BB-sweep length theorem

Clarification to my previous note: the rep12 example only shows that the run-1 branch's immediate local length increase can be +5 (one left token is removed, while bumpSymR can expand a leading rep12 by five). It does not refute the global theorem |sweepBB(L,R)| <= |L|+|R|+4|L|+12; that statement could still follow from an amortized/strengthened induction using the leading run0 shield and subsequent repeat-eat branches.

I ran a source-shaped small-stack simulator over 500,000 random L/R pairs (small run/repeat fields); it found no counterexample to the +4 global estimate. This is only exploratory evidence, not a proof, and the simulator has not been independently checked against Lean. My +5 length theorem is the simple unconditional bound I can prove directly; keep the +4 target open if you have a sharper invariant.
