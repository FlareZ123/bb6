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

A useful phase decomposition also stabilizes exactly across the checked family.
Relative to time `t_n`, the eight newly exposed left cells are first reached in
four consecutive two-cell events:

- positions `-8n-6,-8n-7` at offsets `88n+116, 88n+117`;
- positions `-8n-8,-8n-9` at offsets `88n+132, 88n+133`;
- positions `-8n-10,-8n-11` at offsets `312n+392, 312n+393`;
- positions `-8n-12,-8n-13` at offsets `312n+408, 312n+409`.

The right frontier then advances by eight cells and returns to the next F0 family
at offset \`448n+612\`.

More strongly, if the right zipper is written from the cell immediately right of
the left-edge head through the finite support, the four E0 phase configurations
have the following exact observed words:

- P1: \`00110110 1^(4n+2) (110)^(4n+2) 0110011\`;
- P2: \`0000010110 1^(4n+2) (110)^(4n+2) 0110011\`;
- P3: \`00110110 1^(4n+4) (110)^(4n+4) 011\`;
- P4: \`0000010110 1^(4n+4) (110)^(4n+4) 011\`.

Their exact candidate phase costs are therefore:

\[
  F_n \xrightarrow{88n+116} P1_n
  \xrightarrow{16} P2_n
  \xrightarrow{224n+260} P3_n
  \xrightarrow{16} P4_n
  \xrightarrow{136n+204} F_{n+1}.
\]

The costs sum to \`448n+612\`.  This turns the remaining formalization problem
into three parametric block sweeps plus two fixed 16-step turnarounds, rather than
one opaque 9,922-state automaton.

This is **computational evidence / a formalization target**, not yet a theorem.
The high-value next step is to decompose one (n	o n+1) transition into the
generic `SweepPumping.lean` left/right sweep lemmas, as was done for residual
1106.  If proved, it replaces another 9,922-state BiDFA with a compact symbolic
nonhalting proof.
