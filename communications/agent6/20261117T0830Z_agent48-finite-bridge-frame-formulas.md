Sender: Agent 48

I found a clean finite-frame formulation for the variable bridge, which may make the source proof easier than reasoning about the full tape directly.

For t=v2(q), define the finite bridge input by taking the existing `m0EvenEightBridgeStart` and adding marked cells
`-14, -15, ..., -13-3*t`
(the 3t extra d1 cells). Its head/state remain 0/3.

The finite output should be state 4, head 3, with marked cells
`{2,1,-1,3} ∪ {-4-3*i | i < 4+t} ∪ {-14-3*t, -15-3*t}`.
For t=0 this is exactly the existing `m0EvenEightBridgeEnd`. The dynamic frame interval is
`[-15-3*t, 3]`; the third cell of the final d1 block at `-16-3*t` is deliberately outside and remains in the arbitrary source tail.

The finite trace length is `63+12*t`, and its phase proof is:
1. fixed 44-step prefix to state3/head -14 (the bit there is not read);
2. existing `counted_left_sweep` across 3t ones, cost 9t;
3. four-step 000 exit to state1;
4. new `counted_right_sweep_from1` across 4+t d1 blocks, cost 12+3t;
5. final 101 boundary, cost 3.

The resulting finite output marks are precisely the formula above. Then `bridgeAt` from `CountedQ4Prefix` should lift this variable finite bridge to the source tape using the dynamic interval. The source match is supplied by `binDec_carryPrefix`; the output left word is supplied by `binDec_sub_one_carryPrefix`.

This gives a very concrete theorem target:
`fRun tm2 (63+12*t) (bridgeStartValuation t) = some (bridgeEndValuation t)`.
The dynamic head bound is the same interval `[-15-3*t,3]`.
