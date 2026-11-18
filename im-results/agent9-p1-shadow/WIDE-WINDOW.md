# Wider finite-word source-lift window

**Status: paper derivation only, 2026-11-18.** This is a stronger candidate bound for the finite `ShadowReach`-to-`OddCone` converse. It has not been added to the Lean source or compiled. Keep it in `im-results/`; do not cite it as a kernel-verified theorem or promote it to `results/`.

## Candidate statement

Keep the original feeder-root assumptions and source-coordinate invariant from [CONVERSE.md](./CONVERSE.md), but add the root-size condition
\[
L\le 2z_0+1.
\]
Write
\[
K=N-M.
\]
The proposed sufficient window is
\[
\boxed{K\ge2,\qquad L+M\le 28\cdot 2^K-7.}
\]

Under these conditions, every feeder-rooted `ShadowReach L z0 m z` with \(m\le M\) should lift to an authentic original-source `OddCone` node with the same cost, preserving
\[
b\bmod4=0,\quad d\bmod2=1,\quad
28\le\alpha<56\cdot2^m,\quad
2^m(b+4(L+m-z))=\alpha2^N.
\]
Unlike the existing candidate theorem, the strengthened induction need not assert \(12\le b\) at its final node. The \(12\le b\) bound is needed only when that node is used as the parent of a further inverse edge; the remaining cost budget supplies it there.

Both actual P1 feeders satisfy the extra root-size condition:
- L0: \(L=16q+8\), \(z_0=12q+4\), so \(2z_0+1=24q+9\ge L\).
- L1: \(L=16q+9\), \(z_0=10q+4\), so \(2z_0+1=20q+9\ge L\).

## Proof spine

### 1. A second shadow invariant

For every reachable node,
\[
L+m\le 2z+1.
\]
At the root this is the added hypothesis. For a step, the parent has \(z>0\), and \(z=2^t r\) therefore forces \(r\ge1\). The child equations give
\[
2z'+1=L+m+t+r\ge L+(m+t+1),
\]
which is exactly the invariant at the child. Positivity of every child also follows from \(L\ge8\).

Put \(w=L+m-z\). Then
\[
2w=2(L+m-z)\le L+m+1\le L+M+1
\le 28\cdot2^K-6. \tag{1}
\]
The existing four-unit margin still gives \(w\ge4\).

### 2. Divisibility at every node; size only at nodes with an outgoing edge

The encoded coordinate is
\[
b+4w=\alpha2^{N-m},\qquad \alpha\ge28.
\]
Since \(m\le M\) and \(K=N-M\ge2\), we have \(N-m\ge2\), so \(4\mid b\). This is all that needs to be carried in the induction hypothesis at a terminal node.

Now consider a node that actually has a next shadow edge of depth \(t\). Its child cost is \(m+t+1\), and the theorem's endpoint bound gives
\[
m+t+1\le M.
\]
In particular \(m\le M-1\), hence \(N-m\ge K+1\). The source coordinate therefore gives
\[
b+4w=\alpha2^{N-m}\ge28\cdot2^{K+1}
=56\cdot2^K.
\]
By (1), \(4w=2(2w)\le56\cdot2^K-12\), and consequently
\[
b\ge12.
\]
This is exactly the hypothesis needed by the existing `inverseAt_left_ge_two` lemma. It also implies the weaker \(8\le b\) required by `original_odd_edge_polynomial` and `OddCone.parent`. Thus the stronger left-counter bound is recovered only at an actual parent edge, where the extra unit of cost is available.

### 3. The source safety margin follows from total child cost

Again using \(m+t+1\le M\),
\[
m+t+3\le M+2\le N,
\]
because \(K=N-M\ge2\). This is precisely the existing safety hypothesis of `encoded_shift_divisible` and `original_odd_edge_polynomial`.

Also
\[
N-m\ge K+t+1.
\]
Since \(b\) is divisible by four, it is even, and the encoded coordinate yields
\[
\frac b2+2w=\frac{b+4w}{2}
\ge14\cdot2^{K+t+1}
=28\cdot2^{K+t}.
\]
Combining this with (1),
\[
\frac b2
\ge28\cdot2^{K+t}-28\cdot2^K+6
=28\cdot2^K(2^t-1)+6.
\]
For \(s=d+b/2+3\), the source right counter is odd and hence \(d\ge1\), so
\[
s\ge28\cdot2^K(2^t-1)+10
\ge6\cdot2^t.
\]
The last inequality follows from \(K\ge2\): the coefficient \(28\cdot2^K\) is at least 112; for \(t=0\) the right-hand lower bound is 10, and for \(t\ge1\) it is at least \(112(2^t-1)+10\ge6\cdot2^t\).

### 4. The quotient and exact inverse reconstruction are unchanged

The existing `encoded_shift_divisible` proof gives
\[
2^{t+2}\mid(s+2z).
\]
With \(z=2^t r\), the existing cancellation argument gives
\[
s=2^t C,\qquad C+2r=4Q.
\]
Thus \(C\) is even. The new lower bound \(s\ge6\cdot2^t\) gives \(C\ge6\), so \(c=C-3\) is odd and at least 3. The existing `ancestor_exists_iff_power`, `inverseAt_complete`, `inverseAt_power`, and `original_odd_edge_polynomial` reconstruction then proceeds unchanged.

The key point is that the old proof bounded \(t\) from the coarse estimate \(z<L+M\). The new proof does not need \(z<2^{N-M-3}\) or \(t\le N-M-4\): the *actual child cost* bounds \(m+t+1\), while the second shadow invariant bounds the coordinate offset \(w\).

## Simple feeder corollary

For either feeder, \(L\le N+9\). If \(N\ge2M+2\), then \(K=N-M\ge M+2\ge2\), and
\[
L+M\le N+M+9
=K+2M+9
\le3K+5
\le28\cdot2^K-7
\]
for every \(K\ge2\). Thus \(N\ge2M+2\) is a simple sufficient condition, improving the existing \(N\ge2M+7\) wrapper. The direct window above is much stronger than this linear corollary.

## Exact integer-window comparison

The following maxima are obtained by checking the monotone integer inequality in \(M\). The old columns use the existing direct condition \(L+M\le2^{N-M-3}\); the new column uses \(K\ge2\) and \(L+M\le28\cdot2^K-7\).

| q | N=16q | old L0 max M | old L1 max M | new L0/L1 max M |
|---:|---:|---:|---:|---:|
| 1 | 16 | 8 | 7 | 14 |
| 2 | 32 | 23 | 23 | 30 |
| 3 | 48 | 38 | 38 | 46 |
| 4 | 64 | 54 | 54 | 61 |
| 5 | 80 | 69 | 69 | 77 |
| 6 | 96 | 85 | 85 | 93 |
| 7 | 112 | 101 | 101 | 108 |
| 8 | 128 | 117 | 117 | 124 |
| 9 | 144 | 132 | 132 | 140 |
| 10 | 160 | 148 | 148 | 156 |
| 11 | 176 | 164 | 164 | 172 |
| 12 | 192 | 180 | 180 | 188 |

This extends the existing formal-candidate finite window by 6–8 units for these feeder sizes. It remains a finite-cost statement, not a lift of unbounded paths at fixed q.

## Lean implementation delta

Do not change the existing 587-line candidate until a local Lean preflight is available. The likely low-risk implementation is:

1. Add a paired `ShadowReach` invariant returning \(0<z\) and \(L+m\le2z+1\), with root assumptions \(0<z_0\) and \(L\le2z_0+1\).
2. Add a small helper deriving \(b\bmod4=0\) from \(m\le M\), \(N-M\ge2\), and the encoded coordinate; it should not claim \(b\ge12\).
3. In the step case, use the endpoint hypothesis \(m+t+1\le M\) to derive \(m\le M-1\), \(b\ge12\), and \(m+t+3\le N\).
4. Replace the old \(t\)-bound and old left-counter helper with the inequalities above. Keep \(12\le b\) only locally for `inverseAt_left_ge_two`.
5. Apply the divisibility-only helper to the child coordinate and remove \(12\le b\) from the theorem's final existential.

This is not yet a Lean-checked theorem. The current source leaf remains uncompiled, and the Critic's local-leaf-before-full-CI rule remains in force.

## Scope

This improves only the finite shadow-to-source correspondence. It does not establish an unbounded-cost lift at fixed q, an infinite original-source inverse path, blank-tape forward reachability, P1 nonhalting, or any BB(6) upper bound. The result remains in `im-results/` pending formalization, local compilation, independent source review, and the existing manual source audit.


## Relationship to the exceptional c=1 terminal

The c=1 terminal itself is not a new gap addressed by this window. Let \(B=8u+4=14\cdot2^{N+2}-2(N+2)-16\), the critical hub with right counter 3. The executable inverseAt from \((B,3)\) gives:
- depth 0: \((k,c)=(2u,4u+5)\), whose source child is L0;
- depth 1: \(v=(4u+5-3)/2=2u+1\), \(v/2=u\), so \((k,c)=(3u+1,2u+1)\), whose source child is L1.

Thus both feeders are already in the CountCone rooted at \((B,3)\). A local L0 prefix of cost \(m_0\) prepends one unit to the CountCone predecessor cost; a local L1 prefix prepends two. The final local c=1 reset has depth \(N+3=(N+2)+1\), so Agent 50's existing source_mid_cost_exceptional_last_reset_depth theorem in im-results/agent50-p1-subwall/ExceptionalLastResetDepthSource.lean already covers both feeder cases after these cost shifts. In particular, the affine c=1 predecessor equations are translations of that existing theorem, not a new exclusion or discovery here.

The contribution of this note is only the wider finite shadow-to-source converse window. It should not be presented as new work on the exceptional terminal or as a P1 nonhalting proof.


## Feeder-specific coefficient

The proof uses the alpha lower bound only through inequalities of the form \(\alpha\ge A\). More generally, for any \(A\ge3\), the same argument works with
\[
K\ge2,\qquad L+M\le A\cdot2^K-7,\qquad \alpha\ge A
\]
throughout the path. The lower bound \(A\ge3\) is more than enough for the final \(s\ge6\cdot2^t\) estimate when \(K\ge2\).

The common theorem above takes \(A=28\), which applies to both feeders. But the alpha update is
\[
\alpha'=\alpha+112\cdot2^m(2^t-1)\ge\alpha,
\]
and the L1 root has \(\alpha_0=42\). Therefore L1 alone admits the stronger window
\[
K\ge2,\qquad L+M\le42\cdot2^K-7.
\]
The L0 root has \(\alpha_0=28\), so no analogous improvement follows uniformly at the root. For L1, the maxima under \(A=42\) for q=1..12 are:
\[
14,\ 30,\ 46,\ 62,\ 77,\ 93,\ 109,\ 125,\ 141,\ 157,\ 172,\ 188.
\]
This adds one unit at q=4 and q=7..10 relative to the common A=28 table.
