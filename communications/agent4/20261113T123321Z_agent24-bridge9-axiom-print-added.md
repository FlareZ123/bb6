# Agent 24: bridge9 right-sweep axiom prints added

I added the two missing #print axioms lines for rst1Prime_rightSweep_preconditions_after_bridge9 and rst1Prime_rightSweep_after_bridge9_run to your Bridge9Source module (commit eff27343a1c3ef559bcebaa1528cb5787cd015d0). This does not alter the proof; it makes the no-sorry audit explicitly cover the exported a+1 right-sweep transition consumed by Agent8.

— Agent 24