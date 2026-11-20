# Phase-50 rho-20 cylinder \(a\equiv1238\pmod{3\,188\,646}\): complete root exclusion

**Status:** paper-level infinite-family exclusion inside the residual \(a\bmod486=266\) class. The reset-parent grammar and blank-root chain equivalence are source-certified elsewhere; this parameter-specific proof is not yet Lean-compiled.

Let
\[
P=2\cdot3^{13}=3\,188\,646,\quad a=1238+Pn,
\]
\[
K=97\cdot2^{a-7}+48,\quad p=2^K,\quad
B=(2K+7)2^{K+4-a},
\]
\[
D=(B-16p+2K+1)/3,\quad E=8p+K-D,\quad X=2E+5.
\]
Then \(a\equiv266\pmod{486}\), \(K\equiv2\pmod6\), and \(K+6a\equiv20\pmod{54}\). Also
\[
\frac{2K+7}{2^a}=\frac{97}{64}+\frac{103}{2^a},\qquad
E/p\to21/4,\quad X/p\to21/2.
\]

## Exhaustive first parents

The exact certificate gives \(X\bmod3^{13}=712233\), hence \(v_3(X)=6\). For \(t=0,\ldots,5\), the odd-source coordinates \(2^tX/3^{t+1}\), normalized by \(p\), tend to
\[
7/2,\ 7/3,\ 14/9,\ 28/27,\ 56/81,\ 112/243.
\]
Exactly \(t=0,2,5\) lie in odd-source bands; \(t=1,3,4\) are in gaps. Also \(E/p\to21/4\) is an even-parent gap. Thus the complete parent set of \(E\) is
\[
h_0=\frac{2X}{3}-4p-K-4,\quad
h_2=\frac{8X}{27}-2p-K-3,\quad
h_5=\frac{64X}{729}-\frac p2-K-1.
\]

The \(h_0\)-branch is the same long even-parent chain as in [the 158-cylinder proof](PHASE50-158-CYLINDER-ROOT-EXCLUSION.md). For this cylinder the exact certificate again gives
\[
X_1=2h_0+5\equiv21\pmod{27},\quad
G_0\equiv1\pmod9,\quad A_0=4p+2K+1\equiv0\pmod3.
\]
The explicit \(h_0\) band bounds and terminal leaf \(z_{a-10}\) are unchanged from that proof.

## The \(h_2\)-branch is a leaf

Set
\[
X_2=2h_2+5=\frac{16X}{27}-4p-2K-1.
\]
The certificate gives \(X_2\bmod3^{10}=32799\), so \(v_3(X_2)=1\). Its only possible odd coordinate is \(X_2/3\), whose normalized limit is \(20/27\), strictly below the \(3/4\) lower edge of the level-\(K-3\) band. Also \(h_2/p\to10/9\), in an even-parent gap. Hence \(h_2\) has no parent.

## The \(h_5\)-branch has one parent and then stops

The \(t=5\) source coordinate of \(E\) is in the level-\(K-4\) odd band, giving
\[
h_5=\frac{64X}{729}-\frac p2-K-1,\qquad
\frac{h_5}{p}\to\frac{205}{486}.
\]
This is strictly inside the level-\(K-4\) even-parent band. Its odd numerator is
\[
X_5=2h_5+5=\frac{128X}{729}-p-2K+3
\equiv1595\pmod{3^7},
\]
so \(X_5\not\equiv0\pmod3\): no odd parent exists. The unique even parent is
\[
h_6=2h_5-\frac p2-K+4,\qquad
\frac{h_6}{p}\to\frac{167}{486}.
\]
This lies in the gap between the level-\(K-5\) and level-\(K-4\) even bands. Moreover
\[
X_6=2h_6+5=\frac{256X}{729}-3p-6K+9
\equiv14\pmod{3^6},
\]
so \(h_6\) has no odd parent either. It is a leaf.

Consequently the complete inverse-parent graph is
\[
E\to h_0\to z_0\to\cdots\to z_{a-10},\qquad
E\to h_2,\qquad E\to h_5\to h_6.
\]
Every parent set is exhaustive by the valuation bounds and disjoint dyadic bands. Every terminal node is a non-root leaf, so \(E\) is not in the blank-root reset-parent ancestry.

## Period and exact certificate

Put \(M=3^{14}=4\,782\,969\). Since \(2^P\equiv1\pmod M\), the change in \(K\) under \(a\mapsto a+P\) is
\[
97\cdot2^{a-7}(2^P-1),
\]
a multiple of \(2\cdot3^{14}=3P\). Thus all residues above are periodic with period \(P\). Also \(P/486=6561\), so the cylinder is contained in \(a\equiv266\pmod{486}\). The period-18 law for \(2^m\bmod54\) gives \(K\bmod54=44\) and \(K+6a\bmod54=20\) throughout.

The exact BigInt reproducer is [phase50_266_1238_chain_certificate.mjs](phase50_266_1238_chain_certificate.mjs); it checks the modular divisions and agreement at \(a=1238,1238+P,1238+2P\). The closest limiting source-coordinate margin is \(3/4-20/27=1/108>1/1200\). The fixed-depth branch has at most two parent steps; the standard affine error estimate from \(x-97/64=103/2^a\), \(K/p<2^{-a}\), and \(1/p<2^{-a}\) is far below this margin. The integer endpoint offsets are harmless.

This removes one infinite cylinder inside \(a\bmod486=266\), not the whole class. The other 6560 cylinders in each of the 158, 266, and 482 classes modulo \(P\), all other phase-50 classes, the \(a\bmod54=10,28\) lifts, the residual \(a\bmod18=2\) class, other #746 fatal branches, and BB(6) remain open. This is intermediate paper-level research, not a Lean-certified result.
