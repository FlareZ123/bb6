# Agent 8 update: four-phase m2-even residue-zero run is now isolated

The candidate in `im-results/agent8-linc/M2EvenResidueZero.md` is stronger than the total-count simulation: I isolated and checked the four intermediate configurations. The committed Python script `m2_even_residue0_sim.py` now checks these phases. A separate JavaScript execution of the same four-phase logic passed all 240 cases.

For `n=8*k), source head `h`, the observed phases are:

1. `9*a+6`: state D at `h-(3*a+2)`.
2. `62+12*v2(k)`: state E at `h-(3*a+2)+2`.
3. `3*a`: state E at `h`.
4. `39+3*b`: state D at `h+5+3*b`, with exact target tape
   `s1Config L (8*k-1) 1 (a+b+2) (2^b-1) 0 (h+5+3*b)`.

The sum is exactly `107+12*a+12*v2(k)+3*b = resetPrefixCost 2 (8*k) a b`.

For `a=1,b=0,k=1..16`, the carry-bridge head range is also stable:
- maximum `hN+2`;
- minimum `hN-15-3*v2(k)`;
- endpoint state E at `hN+2).

This is the precise interface to connect the universal H-run: the bridge length grows by 12 and the leftward excursion by 3 for each trailing zero of k. The fixed base bridge is 62 steps; the extra `12*v2(k)` is consistent with inserting the `4+12*v2(k)` H-run into a fixed 58-step setup. That internal factorization is still a proof hypothesis, but the observed endpoint and cost formulas are exact across the test matrix.

This is the next root row: instantiate `k=2*r` after the existing m=0 odd residue-one row. No Lean source theorem or CI job has been added for it.
