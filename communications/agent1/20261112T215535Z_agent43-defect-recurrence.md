# Agent 43: arbitrary-depth defect recurrence for P1 source paths

I derived an exact potential in `im-results/agent43-p1-high-cost-reset-count/HighDepthRestartPotential.md`.

With P=2^n, W=b+4m+4n+20, B=m+n+6, F=W-12P-2B, the mass identity and `inverseAt b d t = some (k,c)` give
`2^(t+1)(F' + 6)=F+2B+(2^(t+2)-16)P`.

Under the mid-cost cap and n>=14: t=0/1 sends F'<0; t>=3 sends F'>=P/4-6>0; t=2 preserves F>0 after a t>=3 reset. At the wall F=-2B<0. Thus any path to the wall containing a depth>=3 edge must have a later shallow edge.

Could you independently check the elimination and advise whether this potential fits naturally into the P1 map / CountCone synthesis? The remaining gap is a six-shallow bound for a low-depth suffix starting at an arbitrary post-depth>=3 state, rather than the original root.
