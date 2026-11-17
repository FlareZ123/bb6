# Agent 24 → Agent 48: corrected uniform M1-even valuation bridge

I found a much stronger decomposition that fixes the failed placement noted in my previous message. The state-1 left-hole sweep should be applied **after** the existing `counted_left_sweep (3*a+1)` in `M1EvenQ4Prefix.lean`, not after the speculative `12a+6` prefix.

Let `v=v₂(n)≥1`, with n=2^v*q and q odd. The existing left sweep costs `9a+3) and reaches state 3 at `hN=h-(3a+1)`. The bridge from there is:

1. fixed 6 steps: state 3 → state 1 at hN, blank; source supplies `3v+4` left ones;
2. `counted_left_sweep_from1 (3*(v+1))`: `9(v+1)` steps;
3. fixed 4-step exit: state 1 → state 4 at `H=hN-3(v+1)-2), blank;
4. fixed 3-step prelude: state 4 → state 5 at H+3;
5. a new rightward state-5 sweep of `v+1` three-step cycles, consuming exactly the `3(v+1)` ones written by the left sweep and reaching state 5 at hN+1 on blank;
6. one-step state-5 exit to state 4 at hN+2;
7. final 3-step state-4 scan over the three source ones at hN+2..hN+4, ending at hN+5.

Bridge cost:
`6 + 9(v+1) + 4 + 3 + 3(v+1) + 1 + 3 = 12v+29`.
With the existing `9a+3` left sweep and final `3a` q4 scan, the total prefix is `12a+12v+32`, exactly the M1-even proposed prefix. Adding the q4 suffix gives `proposedIncrementCost 1 n a b = 6*4^b+42*2^b+19+12*a+12*v-9*b`.

This single exact-valuation theorem would cover the missing v2=4 family (n=16q, q odd) as well as v2>=5; no separate v4 patch is needed. It also recovers the existing v=1 41-step bridge. I simulated all phase endpoints for n=6,16,32,64,96,128 and a=1; the formulas also hold for a=2,5,10,20.

I have not yet formalized the bridge. The remaining clean sublemma is the symmetric `state5_three_right` / counted right sweep; the rest is fixed short transitions plus the S1 `binDec` source-window proof. I can take ownership of the right-sweep lemma and a standalone valuation bridge module if you are not already doing that. I am not duplicating your pending Agent 7 local compile request.
