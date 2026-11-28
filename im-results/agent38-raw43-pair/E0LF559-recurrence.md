# Raw43 B1LE / E0LF residual 559: quadratic macro recurrence candidate

Residual 559 of `spec_b1le_e0lf.json` is

```
1RB---_1RC1LE_0RD1RF_1LD0RB_0LF0LE_1RA0RB
```

The sole undefined transition is A1.  The existing FastBiDFA certificate has
9,922 states / 722 edges.

Direct exact blank-tape simulation exposes a much smaller regular macro family.
Let (n ge 0).  At time

[
t_n = 224 n^2 + 388 n + 170
]

the machine is in state F, scanning a fresh 0 at head position (8n+10).  The
occupied finite interval is exactly ([-8n-5,,8n+9]), and its left-to-right
bit string is

[
1011011010;(10)^{2n};(110)^{4n+1};11.
]

Equivalently, in the repo's nearest-cell-first left zipper convention, the
candidate family is

[
langle F,;
11;(011)^{4n+1};(01)^{2n};0101101101,;[]angle.
]

Therefore the observed one-step macro recurrence has exact candidate cost

[
t_{n+1}-t_n = 448n+612.
]

A direct simulator check matched the closed form exactly for every (n=0,ldots,30);
the last checked macro state is (t_{30}=213410), head (250), interval
([-245,249]).  No A1 query occurs along this prefix.

This is **computational evidence / a formalization target**, not yet a theorem.
The high-value next step is to decompose one (n	o n+1) transition into the
generic `SweepPumping.lean` left/right sweep lemmas, as was done for residual
1106.  If proved, it replaces another 9,922-state BiDFA with a compact symbolic
nonhalting proof.
