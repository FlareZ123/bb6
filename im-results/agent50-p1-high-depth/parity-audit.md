# High-depth residual parity audit

**Status:** intermediate proof audit; not a theorem excluding the (A=2,18) residuals.

## Exact local arithmetic

Write the high-depth parent as ((b_p,d_p,m_p)), and let
[
2^tD=d_p+b_p/2+3,qquad D=c+3,qquad
2k+c+2t+2=b_p+d_p.
]
The source parent guard is (b_p\equiv0\pmod4), so (q=b_p/2) is even. For (t\ge2), reduction of the first equation modulo four gives
[
d_p+q+3\equiv0\pmod4.
]
This yields:
[
d_p\equiv1\pmod4\quad\text{if }b_p\equiv0\pmod8,
]
but
[
d_p\equiv3\pmod4\quad\text{if }b_p\equiv4\pmod8.
]
The parent guard (b_p\equiv0\pmod4) does not distinguish these cases. Thus the often-used implication (d_p\equiv1\pmod4) needs the additional hypothesis (b_p\equiv0\pmod8), or another argument proving it in the residual subcase.

## Reachable counterexample to the generic implication

For (n=190), let (P=2^{190}) and take the blank-root state
[
(b_p,d_p,m_p)=(14P-396,3,0).
]
It is an `OddCone` root. At depth (t=5),
[
X=d_p+b_p/2+3=7P-192,
quad D=X/32=7\cdot2^{185}-6,
quad c=D-3=7\cdot2^{185}-9.
]
Set
[
k=(b_p+d_p-c-12)/2=441\cdot2^{184}-198.
]
Then (c) is odd, (k\) is even and at least six, and both inverse equations hold. The child has (b'=2k-4\ge8) and (b'\equiv0\pmod4), so this is a genuine `OddCone` edge. Nevertheless (d_p=3\pmod4).

This example is a counterexample to the **generic** source claim (t\ge2\Rightarrow d_p\equiv1\pmod4). It does **not** satisfy the special residual equation (49D+14M-6\in\{2P,18P\}), so it does not decide whether a stronger statement holds under (A\in\{2,18\}).

## Parity bookkeeping for the residual table

Let (M=m_0+n=m_p+t+1+n), with (n) even, and (T_1=M+6+3s), where (delta=3s-n).

- If (delta=2), then (s) is even and
  [
  T_1\equiv M\equiv m_p+t+1\pmod2.
  ]
- If (delta=1), then (s) is odd and
  [
  T_1\equiv M+1\equiv m_p+t\pmod2.
  ]

Consequently, assigning (T_1\) parity from (t\) parity alone assumes (m_p\) odd. The mod-7 low-trace leaf correctly retains (I_s=20) with odd (T_1), and (I_s=48) with either parity; it does not itself prove (m_p\) odd. The existing depth bounds give (t=5\) or (6\) for the cost-one (I_s=20) branch, (t=5\) for cost-two (I_s=20), and (t\ge8\) for (I_s=48). Do not remove parity branches using (t\) alone until an (A\)-specific source-history lemma is established.

## Useful compatibility filter

The slack parameter satisfies
[
\delta=3s-n>0,\qquad \delta\equiv -n\pmod3.
]
This is an independent and valid compatibility condition and should be applied before enumerating the (I_s\) candidates.

## Next mathematical task

Either prove, using the full `OddCone` ancestry and the special (A\in\{2,18\}) equation plus the terminal cost cap, that (b_p\equiv0\pmod8) (equivalently (m_p\) is odd in this setup), or keep both (T_1\) parities and their compatible (t\)-parities alive. The root example above shows that a generic local mod-four argument cannot supply the missing lemma.
