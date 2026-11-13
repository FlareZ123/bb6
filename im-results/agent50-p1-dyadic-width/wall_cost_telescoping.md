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


## Quantitative bound on the terminal depth-two suffix

Let \(K\ge1\) be the total number of shallow edges, let the last shallow edge have depth \(\tau\in\{0,1\}\), and let \(r\ge0\) be the number of depth-two edges after it. Write \(s_*\) for the cumulative cost immediately before that last shallow edge. Then
\[
m=s_*+(\tau+1)+3r.
\]
Equation (2), after dropping all negative high-depth contributions, bounds \(N\) by the shallow contributions alone. The \(K\) shallow starting costs are distinct and all at most \(s_*\).

- If \(\tau=0\), the sum of the \(K\) largest possible powers is \(2^{s_*+1}(1-2^{-K})\), and every shallow coefficient is at most 6. Thus
\[
N<6\,2^{s_*+1}(1-2^{-K}).
\]
- If \(\tau=1\), the final shallow coefficient is 4 and the other \(K-1\) coefficients are at most 6. The \(K-1\) largest powers strictly below \(2^{s_*}\) sum to \(2^{s_*}(1-2^{-(K-1)})\). Thus
\[
N<(10-6\,2^{-(K-1)})2^{s_*}.
\]

On the other hand, (1) gives
\[
\frac{N}{2^m}>
\frac{m+n+3}{P},
\]
because \((n+3)S+T-1>0\). Combining the bounds yields the exact necessary inequalities
\[
\boxed{
8^r(m+n+3)<6(1-2^{-K})P\quad(\tau=0),
}
\]
and
\[
\boxed{
8^r(m+n+3)<
\left(\frac52-\frac32\,2^{-(K-1)}\right)P
\quad(\tau=1).
}
\]
For example, if \(K\le5\) and \(r\ge1\), these imply respectively
\[
m+n+3<\frac{93}{128}P,\qquad
m+n+3<\frac{77}{256}P.
\]
These are necessary cost/suffix bounds, not exclusions. They may be useful when combining the terminal depth-two suffix with reset-count lower bounds or the preceding high-depth restart analysis.


## Prefix-start generalization (restart form)

The same telescoping proof works when the path starts at an arbitrary source state \((b_0,d_0,m_0)\), not only at the P1 root. Let \(L\) be the remaining total cost, use relative cumulative costs \(s_0=0,\ldots,s_k=L\), and define \(S,T\) from those relative costs. If the path ends at the wall, then
\[
\boxed{
P(7S-2^L)=
2^L(m_0+L+n+3)+(m_0+n+3)S+T-\frac{d_0-1}{2}.
}
\tag{3}
\]
This follows from the same recurrence after replacing \(B_j\) by \(m_0+s_j+n+6\). Source states have odd \(d_0\), so the final term is an integer.

If \(d_0\le2P-1\), then \((d_0-1)/2<P\). The positive terms on the right of (3), other than this final subtraction, imply
\[
P(7S-2^L)>-P,
\]
so the integer \(N=7S-2^L\) satisfies \(N\ge0\). The weighted-sum argument from (2) now applies with \(N\ge0\): there must be a shallow edge, and the last edge whose depth is not two must be shallow. Hence the suffix after the last shallow edge consists only of depth-two transitions.

This condition applies in particular immediately after every depth-\(\ge3\) edge. Indeed the exact defect update gives
\[
F'=\left(2-\frac8{2^t}\right)P-6+\frac{F+2B}{2^{t+1}},
\qquad F=2P-d-5.
\]
Since \(W\ge0\) implies \(F+2B=W-12P\ge-12P\), for \(t\ge3\) we get
\[
F'\ge \frac P4-6.
\]
Thus the child has
\[
d'=2P-F'-5\le\frac{7P}{4}+1\le2P-1
\]
for \(P\ge8\). Consequently, from the child of **every** high-depth edge, any subsequent source path to the wall must contain a shallow edge, and after its last shallow edge it must be a pure depth-two run.

This recovers the high-depth restart/sign principle from an exact source telescoping identity. It still does not bound how many shallow edges may be needed after a high-depth edge.


## Two-sided pinning by the last shallow edge

The weighted identity gives a lower bound as well as the previous upper bound. Let \(s_*\) be the cost immediately before the last shallow edge, of depth \(\tau\), and let \(K\) be the total number of shallow edges. Every earlier high-depth edge ends at a distinct cost strictly below \(s_*\), and its negative contribution has magnitude
\[
(2^{e_j}-8)2^{s_j}=2^{s_j+e_j}-8\cdot2^{s_j}<2^{s_j+e_j}.
\]
The sum of these magnitudes is therefore less than \(2^{s_*}\). The final shallow edge contributes \(6\cdot2^{s_*}\) if \(\tau=0\), or \(4\cdot2^{s_*}\) if \(\tau=1\); all earlier shallow contributions are nonnegative. Hence
\[
N\ge
\begin{cases}
5\cdot2^{s_*},&\tau=0,\\
3\cdot2^{s_*},&\tau=1.
\end{cases}
\]
Together with the upper bounds on shallow contributions and \(m=s_*+\tau+1+3r\), this pins the normalized wall quantity:
\[
\boxed{
\frac52\,8^{-r}\le\frac{N}{2^m}
<6(1-2^{-K})8^{-r}
\quad(\tau=0),
}
\]
\[
\boxed{
\frac34\,8^{-r}\le\frac{N}{2^m}
<
\left(\frac52-\frac32\,2^{-(K-1)}\right)8^{-r}
\quad(\tau=1).
}
\]
Finally, from (1), using \(S<2^m\) and \(T<m2^m\),
\[
\frac{m+n+3}{P}
<
\frac{N}{2^m}
<
\frac{2(m+n+3)}{P}.
\]
Combining the two displays gives the two-sided product constraints
\[
\boxed{
\frac54P<8^r(m+n+3)<6(1-2^{-K})P
\quad(\tau=0),
}
\]
\[
\boxed{
\frac38P<8^r(m+n+3)<
\left(\frac52-\frac32\,2^{-(K-1)}\right)P
\quad(\tau=1).
}
\]
These bounds are independent of how many high-depth edges occur in the prefix. They sharply locate the product of the terminal depth-two run and the total wall cost, but they still do not by themselves rule out a path.
