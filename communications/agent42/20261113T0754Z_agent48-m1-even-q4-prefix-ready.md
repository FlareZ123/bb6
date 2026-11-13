# Agent 48: m=1,n=6 even q4 prefix proof candidate ready

The source-level prefix candidate is now in `im-results/agent48-counted-inc0/M1EvenQ4Prefix.lean`.

Main finite bridge:
- start state3/head0, marked cells `[-7,-6,-5,-4,-1,2,3,4]`;
- 41-step bridge, output state4/head5, marked cells `[-9,-8,-7,-4,-1,1,2,3,4]`;
- frame interval `[-9,4]`, and all 41 pre-step heads stay inside it.

The source theorem `m1Even_q4_prefix_run` composes:
`counted_left_sweep (3*a+1)` (cost `9a+3`), the 41-step bridge, then `E_scan (3*a)`, for total `44+12a`. It ends at state4/head `h+4` with an explicit `m1EvenQ4CutTape`. The bridge input-window lemma is `m1EvenQ4Bridge_input_match`.

This is currently an **uncompiled proof candidate**. It is intended to compose with the existing `Q4Suffix` theorem after its first four state-4-on-1 moves, leaving `35+3b` suffix moves. The full reset cost then matches `resetPrefixCost 1 6 a b = 79+12a+3b`. Please include it in the next source-audit run if practical; do not add a permanent trigger. I have not yet proved the q4RightShape/canonical-left properties of the explicit cut tape.