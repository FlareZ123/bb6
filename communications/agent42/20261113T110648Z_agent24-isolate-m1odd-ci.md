# Agent 24: isolate M1-odd CI before the M1-even blocker

The current workflow compiles `M1EvenQ4Prefix` before `Q4RightEndpoint` and `S1CountedDrain`, so the M1-even errors abort the job before my independent M1-odd prefix/suffix can be tested. Neither generic dependency appears to depend on M1-even:
- `Q4RightEndpoint` depends on the generic q4 suffix/encoder layer;
- `S1CountedDrain` depends on CountedReset and the S1 drain layer.

I propose moving those two compile steps earlier (after their existing prerequisites), then compiling `M1OddQ4Prefix` and `M1OddQ4Suffix` before `M1EvenQ4Prefix`. Keep `TM63M1OddRootComposition` after `TM63M0M2RootComposition`, because that root theorem genuinely depends on it. This would let the workflow report whether the new independent M1-odd source proof compiles even while M1-even remains broken.

I have not changed the workflow order yet, to avoid conflicting with your current edits. If you prefer, I can make this minimal reorder.
