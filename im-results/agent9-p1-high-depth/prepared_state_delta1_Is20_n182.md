# Delta=1, Is=20 local inverse-grammar suffix witness at n=182

**Status:** exact BigInt intermediate witness; not a BB(6) result and not root-reachable.

This example shows that the delta=1, Is=20 A(0,0) third-terminal branch is locally compatible with the inverse source equations. Its prepared parent has M+3>P, but that fact does not disqualify it under the current RestartPath structure: the previously claimed universal bound M+3<=P is not source-proved. The prepared parent is independently not root-reachable, as shown by the exact height-two root-cone calculation below. This is a local counterexample to local-only arguments, not a surviving BB(6) candidate.

## Construction

Take
\[
n=182,\qquad P=2^{182},\qquad \delta=1,\qquad s=(n+\delta)/3=61.
\]
The A(0,0) terminal equation is
\[
21P=106u+32,\qquad u=(21P-32)/106.
\]
Define
\[
M=14u-n-2,\qquad D=(58P+6-14M)/49,\qquad c=D-3.
\]
For a high-depth inverse edge of depth \(t=4\), put
\[
k=(40P+42D-76)/14,\quad
q=-9D+(40P-76)/7+10,\quad
d=16D-q-3,\quad
m_p=M-n-5.
\]
The high-depth parent is \((b,d,m)=(2q,d,m_p)\). Its exact source equations are
\[
16(c+3)=d+q+3,\qquad
2k+c+10=2q+d,\qquad
14k=40P+42c+50,
\]
and its defect is \(49D+14M=58P+6\). All displayed divisions are integral; the parent satisfies \(b\ge8\), \(4\mid b\), \(d\) odd, \(c\) odd, and \(k\ge2\).

The global RestartPath cost condition would require M+3<=P, but this construction has M+3>P. Thus the prepared parent is outside the source-connected restart domain before root reachability is considered. The depth-four inverse edge gives the restart child \((2k-4,c+4,m_p+5)\). From there, **61 depth-two inverse edges** are legal. They reach the first-shallow parent
\[
b_s=12P-24u-12,\qquad
d_s=2P-4u+1,\qquad
m_s=M-n+183,
\]
with offset
\[
T=M+6+3s=14u+5.
\]
This parent satisfies the A-branch equations \(b_s+18=6d_s\) and \(7d_s+2T=14P+17\), so its scalar restart energy is \(I_s=20\).

Three further depth-zero inverse edges are legal and reach a wall state satisfying
\[
b+4m+4n+20=12P.
\]
Equivalently, the scalar LowTrace starting at \((I,B)=(20,T)\), followed by depths \((0,0,0)\), satisfies the terminal wall equation \(I+112B=384\).

The executable exact check is prepared_state_delta1_Is20_n182.mjs. It verifies every inverse power/mass equation, all parent guards \(b\ge8\), \(4\mid b\), \(d\) odd, all child parameters \(c\) odd and \(k\ge2\), the 61 depth-two transitions, the three depth-zero transitions, and both wall equations.

## Why this is not a blank-root path

The construction has \\(M+3>P\\). An earlier claim that every genuine RestartPath carries \\(M+3\\le P\\) is withdrawn: the current `RestartPath` structure has no such field, and the conditional arithmetic lemmas take it as an explicit premise. Thus the value of M does not by itself disqualify this local suffix. If a root-prefix theorem later proves that bound, the displayed A(0,0) equation would contradict it.

Independently, for this same \\(n=182\\), exact forward enumeration of the blank-tape root cone gives only the depth word \\( (0,0) \\), after which no further parent exists. This proves that the prepared parent is not root-reachable without relying on the withdrawn bound.

The obstruction can be seen directly. At the root,
\[
X_0=d+b/2+3=7P-184
\]
has \(v_2(X_0)=3\), so only depths \(t=0,1,2\) can make \(c+3=X_0/2^t\) even. The child guard \(4\mid b'\) leaves only \(t=0\). At the first child,
\[
X_1=3X_0/2-2
\]
has \(v_2(X_1)=1\), so only \(t=0\) remains. At the second child,
\[
X_2=7X_0/4-4
\]
also has \(v_2(X_2)=1\), but its only candidate depth \(t=0\) gives \(2k\equiv2\pmod4\), so the child fails \(4\mid b'\). Thus the root cone has height exactly two for this \(n\), while the prepared-state high-depth parent has enormous cost \(m_p\).

## Research consequence

- The delta=1, Is=20 A(0,0) terminal equations are not ruled out by local inverse legality, the defect identity, or the LowTrace wall recurrence alone. The proposed bound M+3<=P would exclude this particular construction if it were proved for the relevant root prefix, but no current source theorem supplies it.
- The 93P/128 and 77P/256 caps from wall_cost_telescoping.md require \(r\ge1\) depth-two edges **after** the last shallow edge. They do not apply to this witness, whose last shallow edge is terminal (\(r=0\)).
- For n=182, the root cone height-two theorem independently excludes the prepared parent. Arbitrary longer delta=1, Is=20 LowTrace tails still require a source-connected argument.

This is a deliberately explicit counterexample to an overly strong local claim, not evidence that a six-state Busy Beaver machine exists.
