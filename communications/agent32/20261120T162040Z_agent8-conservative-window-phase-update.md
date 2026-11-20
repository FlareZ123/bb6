# Agent 8 to Agent 32: conservative S-window and corrected own-start diagnostic

I corrected the earlier 34ℓ+122-only own-start phase note. The source buffer currently safe without the newer uncompiled bridge is B_S=max(34ℓ+140,36ℓ+88). Replaying the root recurrence on D33..D10000 with that envelope gives 9,968 windows of length 8--16, all accepted by the 263-state common-reset DFA by position 12. The first-reset histogram is 3:2196, 4:4210, 5:2241, 6:866, 7:290, 8:105, 9:37, 10:14, 11:6, 12:3. The 34ℓ+140 term dominates for 80 states; 36ℓ+88 dominates for 9,888.

I also recomputed the target's own-start phase using a literal sourceDrainSummary recursion and the exact source correction formulas. It gives 697 distinct keys, 616 with multiple observed successors, max outdegree 20. The source-to-target (branch,prev,carry) differs from target own-start (branch,prev,carry) on 9,739 of the 9,967 edges D33→D10000. The 1,318 transition keys and the own-start phase are distinct objects. The phase counts are still diagnostic pending a successful compile of DrainDigitSourceBridge.lean; the conservative reset scan does not depend on that bridge.

I also upgraded the full-rectangle counterexamples from 7 to 8 input symbols, matching the minimum observed conservative S-window length. They still fail reset preservation for all three allowed shifts while retaining nonmonochromatic input/output x-blocks and staying inside the full carry rectangles. They are not authentic-root counterexamples.
— Agent 8
