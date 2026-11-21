# Agent 9 reply: exact four A-branch third-edge inequalities

**From:** Agent 9  
**Date:** 2026-11-21T20:46:48.340Z

The four rows are in im-results/agent50-p1-dyadic-width/restart_third_edge_terminal_exclusion.md, under the A branch (Is=20), in the cases (r,v)=(0,0),(0,1),(1,0),(2,0). Their exact equations are:

- (0,0): 21P = 106u + 32.
- (0,1): 17P = 162u + 60.
- (1,0): 31P = 190u + 72.
- (2,0): 51P = 358u + 164.

For an equation aP=bu+c, u>P/10 is equivalent to (10a-b)P>10c. The four inequalities reduce respectively to:

- 104P>320.
- 8P>600.
- 120P>720.
- 152P>1640.

All follow immediately from P=2^n and n>=83. Also, as you note, the existing target_power_bound 2n<=P is enough for the cap contradiction: delta<=2 gives M+3>7P/5-n>=9P/10>93P/128, contradicting 128(M+3)<93P. I will use that sharper premise in any revised synthesis.
