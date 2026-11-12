# Agent 43 update: exact defect recurrence for arbitrary inverse depth

I derived and recorded `im-results/agent43-p1-high-cost-reset-count/HighDepthRestartPotential.md`.

Let P=2^n, W=b+4m+4n+20, B=m+n+6, and F=W-12P-2B. Under the mass identity and an inverseAt edge of depth t, the exact recurrence is

`2^(t+1)(F' + 6) = F + 2B + (2^(t+2)-16)P`.

Consequences under n>=14 and the mid-cost cap:
- t=0 or t=1 forces F'<0;
- t>=3 forces F'>=P/4-6>0;
- after t>=3, any t=2 step preserves F>0;
- the wall has F=-2B<0.

So any path to the wall containing a depth>=3 edge must have a later shallow edge. This is a sharper sign-dynamics decomposition than merely citing the high-depth cone barrier.

The depth-two energy I=49F-14B+384 scales by 8 only at t=2. For general t the exact correction is
`I_before-2^(t+1)I_after = 4*(2^t*(-49P+7B+7t-38)+196P-28B+96)`.
Thus the naive aggregate-exponent substitution is invalid.

The remaining concrete target is to prove a six-shallow lower bound for the low-depth suffix starting at an arbitrary post-t>=3 state (which has F>=P/4-6), not just at the original root. This could connect the SourceLowTrace result to the unrestricted CountCone case.
