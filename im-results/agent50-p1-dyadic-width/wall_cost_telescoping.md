# Exact cumulative-cost identity for source paths to the P1 wall

This note gives an exact identity for every genuine original-source path from the P1 root to the right-five wall. It has no reset-count or inverse-cost cutoff. It is an intermediate structural theorem, not a P1 halting decision.

Let \(P=2^n\), \(n\ge14\). A source path has states \((b_j,d_j,m_j)\), starts at
\[
(b_0,d_0,m_0)=(14P-2n-16,3,0),
\]
and each edge has inverse depth \(t_j\ge0\). Put
\[
e_j=t_j+1,\qquad s_0=0,\qquad s_{j+1}=s_j+e_j,
\]
so \(s_j=m_j\) and the terminal inverse cost is \(m=s_k\). Suppose the endpoint is on the wall
\[
b_k+4m+4n+20=12P.
\]

Every source state satisfies the mass identity
\[
b_j+d_j+2m_j+2n+13=14P.
\]
Writing \(B_j=m_j+n+6\), the exact inverseAt power equation and \(d_{j+1}=c_j+4\) give
\[
\boxed{d_{j+1}=1+\frac{d_j+14P-2B_j+5}{2^{e_j}}.}
\]
In particular, this is an exact integer recurrence, not a relaxation.

## Telescoping identity

Define the two finite sums
\[
S=\sum_{j=0}^{k-1}2^{s_j},\qquad
T=\sum_{j=0}^{k-1}s_j2^{s_j}.
\]
Then every such source path to the wall satisfies
\[
\boxed{
P(7S-2^m)=2^m(m+n+3)+(n+3)S+T-1.
}
\tag{1}
\]

**Proof.** Set \(x_j=d_j-1\). The scalar source recurrence rearranges to
\[
x_j=2^{e_j}x_{j+1}-14P+2n+6+2s_j.
\]
Unrolling along the path gives
\[
x_0=2^m x_k-14PS+(2n+6)S+2T.
\]
Here \(x_0=2\). The wall equality and mass identity give
\[
d_k=2P+2m+2n+7,\qquad x_k=2P+2m+2n+6.
\]
Substitution and division by two yield (1). \(\square\)

The left factor in (1) is necessarily positive:
\[
N:=7S-2^m>0,
\]
because the right side is positive. There is also a useful exact expression for it. Since
\[
2^m-1=\sum_{j=0}^{k-1}(2^{e_j}-1)2^{s_j},
\]
we have
\[
\boxed{N=-1+\sum_{j=0}^{k-1}(8-2^{e_j})2^{s_j}.}
\tag{2}
\]

## Consequences for the final part of every wall path

1. **At least one shallow edge is necessary.** If every \(e_j\ge3\) (equivalently every inverse depth \(t_j\ge2\)), every summand in (2) is nonpositive, so \(N\le-1\), contradicting (1). Thus every source path to the wall contains an edge of depth \(t=0\) or \(t=1\).

2. **The last edge that is not depth two must be shallow.** Suppose instead that the last edge with \(e_j\ne3\) had \(e_j\ge4\). All subsequent edges then have \(e=3\), and contribute zero to (2). Before that last high-depth edge, the total positive contribution from all shallow edges is at most
\[
6\sum_{i<j}2^{s_i}\le6(2^{s_j}-1),
\]
because the \(s_i\) are distinct nonnegative integers below \(s_j\); all earlier high-depth contributions are nonpositive. The last high-depth edge contributes at most \(-8\,2^{s_j}\). Hence the terminal \(N\) would be negative, again contradicting (1).

Consequently **the path ends with a depth-zero or depth-one edge, followed by zero or more depth-two edges, and no depth-three-or-greater edge occurs after that final shallow edge.** Equivalently, after the last shallow edge the entire remaining suffix consists of depth-two transitions.

This is an all-count, all-cost restriction on genuine source histories to the wall. It does not rule out high-depth edges earlier in the path; such an edge must be followed later by another shallow edge. It also does not by itself bound the number of shallow edges or exclude the wall.

## Why this is useful

The remaining high-depth restart problem can now be organized around the prefix ending at the **last** shallow edge. The suffix after it is exactly a depth-two run, so its backward dynamics are governed by the affine recurrence already recorded in the Agent43 communication:
\[
u_{r+1}=8u_r+146,\qquad s_{r+1}=s_r+6
\]
for \(u=b-6d\) and \(s=b+d\) under reverse depth two. The new identity supplies a source-certified reason that this is the only possible terminal suffix after the final shallow edge, rather than merely a convenient case split.

No claim is made here that the preceding prefix is low-depth, that the wall is unreachable, or that BB(6) is determined.
