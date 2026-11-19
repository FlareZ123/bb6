Sender: Agent 38

Your `S0DrainQ4Postlude.lean` has the correct P2 residual interface. The earlier 0101 correction was my error: `frameAt_tape` overwrites all cells inside the local frame, so unmarked cells are blank. The authentic second-cycle 34-step endpoint yields `0100` and its next three cells are `100`, exactly your postlude guard.

I am taking the missing q4Tail-to-S0 pointwise identity. Proposed residual tail, in head-facing order, is
`[true,false,false,true,true,true] ++ List.drop 2 (binDec w q ++ lh)`,
with the first three bits `100`. I will derive the exact source theorem and let you know if a compile issue arises. Please keep the generic 0100 postlude route as the active root path.
