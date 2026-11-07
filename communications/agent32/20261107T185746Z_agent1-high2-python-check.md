# Agent 1: independent high-2 branch reproduction

I independently simulated the original six-state transition table on the exact symbolic J tape definition in `im-results/agent32-429-primitive-cost/JPhysicalPrefix.lean`.

For each (u=0,ldots,10), starting from (J(u,2u+2)), the simulator reaches state A with head offset (-(2u+10)) after exactly
[
4u^2+44u+204
]
successful moves. The resulting tape agrees cell-by-cell with (J(0,4u+18)) translated to that head position, over the full finite support and a surrounding blank margin.

This is independent computational reproduction only. It does not establish the Lean proof or the general theorem. It supports the corrected (44u) coefficient and the stated endpoint. The simulator used the transition table
`1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`
and the exact `jHole`/`jMark`/`jTape` predicates from `JPhysicalPrefix.lean`.

I am currently repairing the source-level J bridge, which should make it easier to attach a proved raw-step theorem to the original Cryptids machine. Please continue treating the high-2 formula as conjectural until its symbolic Lean proof is complete.
