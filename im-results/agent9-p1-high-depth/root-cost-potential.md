# One-dimensional cost potential for the original OddCone

**Status: exact algebraic identity; a research handle on root reachability, not a BB(6) solution.**

Fix the original root
[
(b_0,d_0)=(14P-2n-16,3),\qquad P=2^n,
]
and write its conserved mass as
[
C=b_0+d_0=14P-2n-13.
]
For any `OddCone` state ((b,d,m)), the mass identity is
[
b+d+2m=C.
]
Since (d) is odd, put
[
x=\frac{d-1}{2},\qquad K=\frac{C+7}{2}=7P-n-3.
]
Then
[
b=C-(2x+1)-2m=2(7P-n-7-x-m).
]
Consequently, the parent guard (4\mid b) is equivalent to
[
x+m\equiv1\pmod2,
]
and (b\ge8) is equivalent to (x+m\le7P-n-11).

## Exact transition

For a source edge of depth (t\ge0), let the child be ((b',d',m')), with
[
m'=m+t+1,qquad d'=c+4.
]
The source power equation is
[
d+\frac b2+3=2^t(c+3)=2^t(d'-1).
]
Using (b+d+2m=C) and (d=2x+1), its left side simplifies exactly to
[
d+\frac b2+3=K+x-m.
]
Since (d'-1=2x'), where (x'=(d'-1)/2), this gives the one-dimensional recurrence
[
\boxed{\quad 2^{t+1}x'=K+x-m,\qquad m'=m+t+1.\quad}
]
The child can itself be a parent only if (x'+m'\) is odd and its corresponding left counter is at least 8.

## Cost-weighted potential

Define
[
R(b,d,m)=2^m x=2^m\frac{d-1}{2}.
]
Multiplying the transition recurrence by (2^m) yields
[
\begin{aligned}
R'&=2^{m'}x'
 =2^{m+t+1}x'\\
 &=2^m(K+x-m)\\
 &=R+2^m(K-m).
\end{aligned}
]
Thus every source edge has the exact depth-independent increment
[
\boxed{\quad R'-R=2^m(K-m).\quad}
]
For a path from the root to cost (M), with transition-start costs
[
0=m_0<m_1<\cdots<m_{r-1}<M
]
and (m_{i+1}-m_i=t_i+1), this telescopes to
[
\boxed{\quad
2^M x_M
=1+\sum_{i=0}^{r-1}2^{m_i}(K-m_i).
\quad}
]
Equivalently, root reachability imposes a weighted subset-sum condition on the visited cost levels. The gaps are not arbitrary: each is (t_i+1), and the corresponding quotient must satisfy the source guards. This may be a useful route to a compressed root-cone analysis.

## Immediate root obstruction when (n\equiv0\pmod4)

At the root (x_0=1,m_0=0), the source power is
[
K+x_0-m_0=K+1=7P-n-2.
]
For (n\ge4) divisible by 4, this is (2\pmod4), so its 2-adic valuation is exactly 1. Since (d'-1=2x') is even, the source equation forces (t=0). The resulting child has
[
x_1=\frac{K+1}{2},\qquad m_1=1.
]
Here (x_1) is odd, so (x_1+m_1) is even. The child therefore fails the necessary parent parity (x+m\) odd. This recovers the one-edge root-cone obstruction in a compact coordinate system.

For (n\equiv2\pmod4), the first valuation is at least 2 and the root tree can branch. The recurrence above isolates the remaining problem: determine which bounded-gap cost sets can satisfy the weighted sum and all intermediate parity/positivity constraints. The n=808 prepared-state witness is excluded by the immediate root obstruction; it is only a local-suffix example.
