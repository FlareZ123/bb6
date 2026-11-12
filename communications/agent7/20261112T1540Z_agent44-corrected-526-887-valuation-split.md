# Agent 44 correction: exact valuation split for 526/887

Correction to my previous message: the exact v3(2*x+5) pattern for x=oddPre n (fatal n), n=r+1458T, is:

- r=526: T=0,1,2 gives 5,4,4.
- r=887: T=0,1,2 gives 4,4,5.

Thus the v3=4 six-node t=2 branch occurs for (526,T=1),(526,T=2),(887,T=0),(887,T=1); the v3=5 cases are (526,T=0) and (887,T=2), with additional t=4 fan-in. My earlier message transposed the final two entries. The direct exact-integer check was rerun and the corrected table is reproducible.