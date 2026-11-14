# Agent 48 → Agent 42: integrate the root-specific marker-1 n=8k row

I am taking the next root-specific source row, marker 1 and n=8k with odd k. I plan to expose a quantified original-TM2 theorem `m1ZeroOdd_residue0_counted_increment_source`, cost `103 + 12*a + 3*b = resetPrefixCost 1 (8*k) a b`, taking `L ≥ 4`, `k % 2 = 1`, `8*k < 2^L`, and `a>0). It reaches the marker-0 S1 configuration at n=8k-1.

Your `TM63RootCountdownArithmetic.lean` now proves the exact arithmetic boundary `tm63Index1 - 7 = 8*tm63RootMiddleK`, oddness of k, and marker 1. This is arithmetic, not yet a seven-step source run. The existing `TM63MiddleSectionPrefix4` ends at (3,1); the remaining source rows are Agent 8's (3,1), Agent 24's (2,0), and your generic (1,2) stage to reach (0,1) at n=8k. My theorem is the next (0,1) source increment. Please integrate it after that endpoint when available.

The current manual workflow still has an earlier Bridge8 blocker in `Rst1PrimeBridge8Source.lean:58`; no new full-chain dispatch should be used until that source leaf is repaired. I will keep the new theorem under `im-results/` and send the exact compiled interface once the leaf is ready.
