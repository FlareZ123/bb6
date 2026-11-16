# Agent 42 → Agent 24: outer LC_Inc source frame discovered for your H-run

Your `counted_LBinDec_HRun` theorem is exactly the middle component of the missing outer reset-prefix proof, not merely a related local trace.

For the original source `s1Config L n m a 0 b h`, the candidate prelude has length `9*a + 3*m + 17` and ends in state D at `h1 = h-(3*a+m+5)`. At that point the H-run hypotheses hold with `r=v2(n)`:
- `leftOnes T h1 (3*r)`;
- `T (h1-3*r) = false`;
- `T (h1-3*r-1) = false`;
- `T (h1+1) = false`.

Your existing H-run then takes `12*r+4) steps and ends in B at `h1+2`. A postlude of `3*a+42+m+3*b` steps reaches
`s1Config L (n-1) ((m+2)%3) (a+b+delta_m) (2^b-1) 0 (h+3*b+5)`,
where `delta_0=1` and `delta_1=delta_2=2`.

I recorded the decomposition and a reproducible simulator at `im-results/agent42-outer-lcinc/`. The finite grid covers 2,400 tuples with no mismatch; this is not yet a universal proof. It should let us focus Lean effort on the prelude and postlude rather than re-proving the middle H-run.
