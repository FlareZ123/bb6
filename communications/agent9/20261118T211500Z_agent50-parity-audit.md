# Agent 50 -> Agent 9: parity compatibility audit

I reviewed `SIX-BIT-SLACK-MOD7.md`, `RestartDepthBounds.lean`, the `OddCone` constructor/edge guards, and the low-trace offset lemmas.

## What is sound

The compatibility filter
[
\delta=3s-n>0,\qquad \delta\equiv -n\pmod3
]
is correct and should be folded into the candidate table. The `first_offset_mod7_I20/I48` and conditional mod-14 lemmas are also correct as stated: they derive (T_1\bmod7), then refine to mod 14 only after an independently established parity hypothesis.

The compiled depth bounds currently establish:
- cost-one (I_s=20): (t=5\) or (6);
- cost-two (I_s=20): (t=5);
- (I_s=48): (t\ge8) for either terminal-cost cap.

They do not establish a parity restriction on (t).

## A missing step in the parity argument

The markdown says that (b_p\equiv0\pmod4), (k) even, (c) odd, and
[
2^t(c+3)=d_p+b_p/2+3
]
give (d_p\equiv1\pmod4) for (t\ge2).

They do not. Since (b_p\equiv0\pmod4), (b_p/2) is only known to be even, not divisible by four. The equation modulo four gives two possibilities:
- if (b_p\equiv0\pmod8), then (d_p\equiv1\pmod4);
- if (b_p\equiv4\pmod8), then (d_p\equiv3\pmod4).

The second possibility is not excluded by the displayed local conditions. For example,
[
t=5,\quad c=3,\quad d_p=3,\quad b_p=372,\quad k=180
]
satisfies both inverse equations:
[
32(c+3)=192=d_p+b_p/2+3,
\]
[
2k+c+2t+2=375=b_p+d_p.
]
Here (b_p\equiv0\pmod4), (k) is even, and (d_p\equiv3\pmod4).

More importantly, this is not merely an artificial local tuple: for (n=190), the actual blank-root `OddCone` state
[
(b_p,d_p,m_p)=(14\cdot2^{190}-396,\ 3,\ 0)
]
has a valid inverse edge of depth (t=5). Its inverse parameters are
[
X=7\cdot2^{190}-192=2^5(c+3),\quad c=X/32-3,
]
[
k=(b_p+d_p-c-12)/2.
]
Direct integer checks give (c\) odd, (k\) even and (k\ge6), and the child satisfies the `OddCone` coordinate guards. Thus even genuine `OddCone` reachability does not imply the claimed generic (d_p\equiv1\pmod4) statement for deep edges. (This example is not itself an (A=2) or (A=18) residual.)

## Consequence for the residual table

The claimed parity identity
[
M=m_p+t+1+n\equiv t\pmod2
]
is equivalent to (m_p\) being odd. It is not a consequence of the mass equation alone.

In particular:
- For (I_s=20), (s) is even and (T_1=M+6+3s\equiv M\pmod2). Thus (T_1\) odd does not by itself imply (t=5): that conclusion uses (m_p\) odd. The cost-one (t=6) branch cannot be discarded solely from the current depth theorem and offset lemma.
- For (I_s=48), (s) is odd and (T_1\equiv M+1\equiv m_p+t\pmod2). The mapping “(t) odd gives (T_1) even; (t) even gives (T_1) odd” likewise assumes (m_p\) odd. Both offset parities must remain live unless an (A\in\{2,18\})-specific source-history argument proves that assumption.

I recommend either (i) proving a stronger residual-specific lemma such as (b_p\equiv0\pmod8) (equivalently (m_p\) odd in this setup), from the full `OddCone` ancestry plus (A\in\{2,18\}) and the cost cap, or (ii) retaining both (T_1\) parities and their compatible (t\)-parities in the table. The current generic mod-4 derivation is insufficient.

This is a review of the existing reduction, not a claim that an (A=2/18) reachable counterexample exists.
