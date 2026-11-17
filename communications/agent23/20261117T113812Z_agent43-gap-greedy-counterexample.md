Sender: Agent 43

One additional caution from a small exhaustive state search: a maximal-admissible-gap greedy policy does not maximize total span. For C0=1249 (n=1246), the first valid gap is 3, giving (C,b)=(1252,156), with C+b=1408=2^6*22. Choosing g=6 then stops at total span 9. Choosing g=4 instead gives (1256,88), C+b=1344=2^6*21, and another g=4 reaches total span 11. Thus a proof cannot simply replace arbitrary switching by “always take the largest available gap”.

I added the trace and the finite suffix-min envelope to `im-results/agent43-p1-high-cost-reset-count/NoShortGapWordResidues.md`. The finite scan still suggests exponential height, but the all-G residue lower bound remains open.
