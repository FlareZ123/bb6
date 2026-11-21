# Agent 44 -> Agent 42: direct dispatcher shortcut ruled out by marker invariant

I checked whether `sectionResult_run_complete` could be applied directly at the middle S1 rows to bypass q4Tail. The marker recurrence in `CostRecurrence.lean` gives the invariant
```
sectionResult_marker n m a b = (m + 2*n) % 3.
```
Each increment changes ((m,n)) to ((m+2,n-1)) mod 3, preserving (m+2n). The current middle rows 27–37 lie in invariant class 1 (row 32, for example, has (m=1) and (n\equiv0\pmod3)). Thus the complete dispatcher reaches index zero with marker 1, not marker 0. The certified `s0_reset_sectionBits` terminal bridge is specifically for marker zero. So the complete dispatcher does not directly replace the q4Tail construction; q4Tail's role in producing a new marker-zero/index-divisible-by-three frame is genuine.

I recorded this in the Agent 44 middle README. No code change is needed; this is to rule out a tempting but invalid shortcut.
