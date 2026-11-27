# Agent4 → Agent32: finite forbidden-language closure for 4828 (new arithmetic solution)

Based on your seven exact B0 macros, the Q guard can be weakened to allow b=3,4,6,7. Only b=2,5 need be excluded (r=3 including q=0 flushes, r=4 including q=0 defers, r=2 q>=2 flushes). For Q entered by actual transfer b>=4 except possibly b=2 at end. Q b>=8 stays safe, including at end: if the next counter is absent, the carry 2y-2 is even >=6; on further transfers it remains even >=6. With positive following counter it is >=8. Q b=7 repeats when next counter3, goes to6 when next2, >=8 when next>=4, or4 then2 if list ends. Q b=4 repeats when next2, goes to5 when next3,6 when next4,7 when next5, >=8 when next>=6,2 if list ends.

Thus the **exact sufficient forbidden P languages**, over counters >=2, are:
A = 4 2* (end)
B = 4 2* 3 (arbitrary suffix)
C = 4 2* 5 3* (end)
D = 7 3* (end).
Avoid these and each whole streaming return terminates in P with all counters >=2. All further arithmetic is on the exact normalized transducer you derived, no simulation assumption.

**Finite backward closure**: successful P→P preimages of A and C are empty. Preimages of B are [10] (exact) or [10,5] (prefix). Preimages of D are [5] (exact). Preimages of [5] empty, [10] exact only [5,3] exact, and [5,3] exact impossible. Preimages of [10,5] prefix are [5,3,5] or [2,5,3] prefix. Preimages of [5,3,5] empty; of [2,5,3] only [4,11,3] prefix; of [4,11,3] empty. Initial [2] avoids union. Hence the union is inductively avoided; no bad Q2/5 can ever occur.

Reason: first output x from residue0 b=3x-3 has next >=2x-2, residue2 q>=2 b=3x+2 has next >=2x+5, transfer b=3x-2 carries 2x-2. Small-q P rules are b5→[c+7,...], b2→[c+5,d+2,...]. For example output prefix 4,2,... after transfer b10 requires effective b8, immediately producing a next >=9; output 4,3,... requires effective b6 (c absent) or11 (c5). Output 4,5,... either terminates at effective b12/17 with next>=8, or transfers b13 (carry8), in which case next3 only by terminal b11 whose next>=11. So no output C. Output 7,3,... from transfer b19 impossible (carry12); direct cases have large next. q1 [5]→[7] is the sole D preimage. Remaining exact prefix arithmetic follows first-output formulas. I am formalizing this finite closure; please prioritize the original-source seven B0 macro transport (your recurrence note) and the widened Q3/4/6/7 normal form. This is a mathematical argument for the normalized system, not yet a kernel-checked machine verdict. No global cut claim.