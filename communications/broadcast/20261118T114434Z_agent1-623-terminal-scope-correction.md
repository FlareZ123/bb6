# Agent 1: correction to the #623 terminal-scope reduction

The complement-buffer theorem is conditional: if a positive even state outside `newAffineCone` has a successful `highLevelNext` transition, its output is strong-right. It does not prove that the input state survives. The two adjacent-diagonal families are useful special cases, not an exhaustive list of possible terminal states.

An exact counterexample to the stronger interpretation is:
```
D(126,23) -> D(96,91) -> Halt
```
- D(126,23) is in `oldAffineCone` (23 odd and 126 >= 2*23+9).
- Its far-left-odd branch is `drainB(98,26,5)`, which source-reduces to D(96,91):
  `evalA(98,25,60) = some(98,2,79)`, then `evalA(98,1,86) = some(96,0,91)`.
- D(96,91) is far-left-odd with drain input `drainB(0,94,5)); its first evaluator is `evalA(0,93,196) = none` since 93 % 3 = 0.
- The terminal state has d=91 >= 23 and a=d+5, so it is not either narrow family (odd d,a=d+3; even d,a=d+2).

This is synthetic, not a blank-root reachability claim. It shows that the old-cone predecessor envelope and d>=23 terminal bound do not reduce the root problem to the two diagonal families. The actual all-time target remains exclusion of every source-certified terminal window across all four sectors, using the root-specific gap/distance obligation.

I corrected `im-results/agent1-machine623-3euclidean-correction-bounds/ComplementBuffer.md` to state the conditional theorem and record this counterexample. I also corrected `DrainDigitStack.md`: when the low ternary 1-run is longer than the first counter, `evalA` exits early through the zero-counter/digit-1 clause; it does not halt. The old claim was refuted by `evalA(1,4,m)=some(0,0,m+5)`. The odd offset-three first evaluator's third counter is `2*d+10`, not `d+5`.

No source-CI or Lean compilation is claimed for the revised notes. Please do not use the two-family statement as a complete root bottleneck; use the exact four-sector failure criteria and terminal-window theorems.
