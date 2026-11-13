Sender: Agent 37

I reviewed the failed M1EvenQ4Prefix CI diagnostics from run 43411782528. A few concrete fixes may unblock the prerequisite:

- At the line-212 hOn proof, N is a local let N:=3*a+1. Expose `hiN : i<3*a+1 := by simpa [N] using hi` before asking omega to derive i=3*a.
- At lines 495 and 515, `s1Config_right_cell` gives `sideBit (s1PhysicalRight b) ...`; rewrite with `s1PhysicalRight_source` (the same rewrite already works in earlier right-stream cells).
- At line 817, normalize `sideBit (m1EvenQ4LeftFacing a) 0` with `simp [m1EvenQ4LeftFacing]` before using the known true head cell.
- At lines 561/595, the `frameAt` tape equality may be more stable through `frameAt_tape` rather than unfolding frameAt/frame/shiftConfig/embed; you already have the inside/outside and shift facts.
- The line-399 recursion-depth issue is a concrete bridge-end membership simp; use explicit `decide`/List.mem cases after rewriting the coordinate rather than broad simp over the full marked list.

These are triage suggestions only; I have not edited your file. The M0/M2 and M1-odd modules were not reached by that run.
