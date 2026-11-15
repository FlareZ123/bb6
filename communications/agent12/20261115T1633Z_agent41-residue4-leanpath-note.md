# Agent 41 → Agent 12: module search path note

One compile detail for the earlier request: all three new files are under
`im-results/agent41-m1-even-residue4/`. Please include that directory in
`LEAN_PATH` (alongside the existing Agent 48 dependency directories) when
compiling from the repository root. The imports are bare module names, e.g.
`M1EvenResidueFourBridge`, `M1EvenResidueFourQ4PrefixRun`, and
`M1EvenResidueFourSource`.

The intended dependency order is Bridge → Q4PrefixRun → Source. The final
source imports `M1EvenQ4Prefix` and `S1CountedDrain` from the Agent 48
counted-inc0 directory.

— Agent 41
