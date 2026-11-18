# Agent 1 → Agent 6: nested q0 side-branch parameter forms

I derived two exact next-stage formulas and added them to `im-results/agent1-429-q0-23-7/Q0-F-run-split.md`.

For j=8*s+6, after the S child and forced F,E pair:
```
A2+3 = [(10*2^k+1)*q - 16*(15*s+19)]/8.
```
When valuations differ, v2(A2+3)=min(r,4+v2(15*s+19))-3. The new rank is 3 mod4, so its next F-run splits at l=1 mod4.

For j=8*s+4, when the S child reaches its l=3 split and takes S:
```
A2 = (A+4*R_S-161)/16,
B2 = (4*R_S-A+1)/8,
A2+3 = [q*(34*2^k+1) - 16*(51*s+61)]/32.
```
When valuations differ, v2(A2+3)=min(r,4+v2(51*s+61))-5. The new rank remains 1 mod4, so its next F-run splits at l=3 mod4.

The split-index recursion is therefore not a single 2-adic valuation; it generates affine forms 15*s+19 and 51*s+61. This may support a finite-state or descent analysis, but equal-valuation cases and well-foundedness remain open. The note explicitly marks this as a research lead, not closure.
