# Machine 746: an infinite rho-20 subfamily excluded from the blank-root reset cone

**Status.** This is a paper-level arithmetic theorem over the original-source first-reset inverse grammar. The exact parent relation and its equivalence with genuine source first resets are kernel-certified in [FirstInverseComplete.lean](../im-results/agent10-cascade/FirstInverseComplete.lean); strict decrease of every parent is kernel-certified in [ResetParentStrict.lean](../im-results/agent10-cascade/ResetParentStrict.lean). The arithmetic specialization below has not yet been formalized in Lean. It excludes an infinite subfamily of candidate fatal heights, not the whole machine.

## Theorem

For every integer \(a\ge18\) divisible by \(18\), set
\[
K=97\cdot2^{a-7}+30,\qquad
p=2^K,\qquad
r=K+4-a,\qquad
B=(2K+7)2^r,
\]
\[
D=\frac{B-16p+2K+1}{3},\qquad E=8p+K-D,\qquad X=2E+5.
\]
Then \(K\) is an admissible rho-20 member of the \(t=0,q=0\) fatal-source family, but
\[
E\notin\operatorname{ResetChain}(2).
\]
Equivalently, this candidate fatal height is not reached from the blank root by the original machine's first-reset chain.

## Proof

### 1. Candidate and modular data

The chosen parameter satisfies
\[
2K+7=97\cdot2^{a-6}+67,\qquad
x=\frac{2K+7}{2^a}=\frac{97}{64}+\frac{67}{2^a}.
\]
For \(a\ge18\), this lies in \([97/64,13/8]\). Since \(18\mid a\), the exponent \(a-7\) is congruent to \(11\pmod{18}\). The identities \(2^{11}\equiv50\pmod{54}\), \(2^{18}\equiv28\pmod{54}\), and \(50\cdot28\equiv50\pmod{54}\) give
\[
K\equiv20\pmod{54},\qquad K+6a\equiv20\pmod{54},
\]
so \(K\equiv2\pmod6\) and the candidate is in the rho-20 phase.

For the modulus \(81\), the three possibilities for \(a\pmod{54}\) give the following complete residue table (using \(2^{54}\equiv1\pmod{81}\)):
\[
\begin{array}{c|rrrrrr}
a\bmod54 & K\bmod81 & r\bmod54 & 2^r\bmod81 & B\bmod81 &
(80p+2K+13)\bmod81\\ \hline
0  &20&24&10&65&22\\
18 &74&6 &64&38&49\\
36 &47&42&37&11&76
\end{array}
\]
In all three rows \(p=2^K\equiv31\pmod{81}\). The table therefore gives
\[
3X=80p+2K+13-2B\equiv54\pmod{81},
\qquad
9X_1=248p-8B-10K+25\equiv27\pmod{81}.
\]
The exact source-family identity is
\[
3X+2B=80p+2K+13.
\]
The next odd-parent numerator is
\[
X_1=2h_0+5=\frac{248p-8B-10K+25}{9},
\]
where \(h_0\) is defined below. Thus
\[
3X=80p+2K+13-2B\equiv54\pmod{81},
\]
\[
9X_1=248p-8B-10K+25\equiv27\pmod{81}.
\]
It follows that
\[
X\equiv18\pmod{27},\quad v_3(X)=2,
\qquad
X_1\equiv3\pmod9,\quad v_3(X_1)=1. \tag{1}
\]

### 2. The first two inverse parents are unique

The source-exact odd ResetParent arm is
\[
2u+5=3^{t+1}d,\quad d\ \text{odd},\quad
6\cdot2^k+1\le2^td\le8\cdot2^k-1,
\]
with
\[
2(2^td)=8\cdot2^k+h+k+5.
\]
The Lean theorem reset_parent_iff in FirstInverseComplete.lean proves that this grammar is equivalent to a genuine original-source first reset. In particular, every \(t\) allowed by the valuation must be checked; no condition \(3\nmid d\) is present.

First,
\[
E=\frac{40p+K-B-1}{3},\qquad
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p}.
\]
The bounds \(97/64\le x\le13/8\) and \(K\ge266\) imply \(4p<E<6p-1\). Hence \(E\) has no even parent.

From the exact identity and \(B=16xp\),
\[
\frac Xp=\frac{80-32x}{3}+\frac{2K+13}{3p}.
\]
Since \(x\le13/8\), the first term is at least \(28/3\). Since \(x\ge97/64\) and \((2K+13)/p<1\) for \(K\ge266\), the sum is less than \(21/2+1/3=65/6\). Thus \(28/3<X/p<65/6\), and \(P_0=X/3\) satisfies \(3p<P_0<4p\), as used below. Since \(X\) is odd, \(P_0\) is odd.

By (1), the only possible odd exponents at \(E\) are \(t=0,1\). The maximal-exponent coordinate is
\[
P_1^{(E)}=\frac{2X}{9},
\qquad
\frac{56}{27}<\frac{P_1^{(E)}}p<\frac{65}{27}.
\]
It lies in the gap \((2p,3p)\), so \(t=1\) is impossible. On the other hand \(P_0=X/3\) satisfies
\[
3p<P_0<4p,
\]
and is therefore in the \(t=0\) odd-source band at level \(K-1\). Put
\[
h_0=2P_0-4p-K-4.
\]
Then
\[
2E+5=3P_0,\qquad
2P_0=8\cdot2^{K-1}+h_0+(K-1)+5,
\]
so \(\operatorname{ResetParent}(h_0,E)\) holds.

Its odd numerator is \(X_1=2h_0+5\), and (1) gives \(v_3(X_1)=1\). Thus only \(t=0\) is possible at \(h_0\).
We also need to show that \(h_0\) has no even parent. Since \(x=97/64+67/2^a\),
\[
\frac Xp=\frac{21}{2}-\frac{32\cdot67}{3\cdot2^a}+\frac{2K+13}{3p}<\frac{21}{2}.
\]
The last inequality follows from \(2^a<2K+7\) and
\(2144\cdot2^K>(2K+13)(2K+7)\), valid for \(K\ge266\). Hence
\(28/9<P_0/p<7/2\), and
\[
\frac{h_0}{p}=2\frac{P_0}{p}-4-\frac{K+4}{p}
>\frac{20}{9}-\frac{K+4}{p}>2,\qquad
\frac{h_0}{p}<3.
\]
Since \(h_0\) is even, \(h_0<3p\) places it below the next even-parent band, which begins at \(3p-1\); the preceding band ends at \(2p-3\). Thus \(h_0\) has no even parent.

The exact expression for \(X_1/p\) is
\[
\frac{X_1}{p}
=6-\frac{128\cdot67}{9\cdot2^a}-\frac{10K-25}{9p}
\in(5,6).
\]
Therefore \(P_1=X_1/3\) is odd and lies in the odd-source band at level \(K-2\), and the unique parent of \(h_0\) is
\[
y_0=2P_1-2p-K-3.
\]

### 3. The remaining even-parent chain ends in a gap

Set \(L=K-2\) and \(D_0=2p-y_0\). Direct substitution yields
\[
D_0=\frac{17152\cdot2^{K-a}+47K+31}{27},
\qquad
D_0+L=\frac{17152\cdot2^{K-a}+74K-23}{27}. \tag{2}
\]
In particular, \(D_0>3\).
Define
\[
D_{j+1}=2D_j+L,\qquad y_j=2p-D_j.
\]
Then
\[
D_j=2^j(D_0+L)-L
\]
and
\[
\frac{D_j}{p}
=\frac{17152}{27\cdot2^{a-j}}
+\frac{2^j(74K-23)}{27p}-\frac Lp. \tag{3}
\]
For \(j\le a-10\), the absolute value of the last two terms in (3) is less than \(K^2/2^K<1/100\). Indeed \(2^a<2K+7\), so \(2^j\le2^{a-10}<(2K+7)/1024\), and \(K\ge266\).

At the two decisive indices,
\[
\frac{D_{a-11}}p=\frac{67}{216}+\varepsilon_{a-11}<\frac12,
\qquad
\frac{D_{a-10}}p=\frac{67}{108}+\varepsilon_{a-10}\in\left(\frac35,1\right),
\]
with \(|\varepsilon_j|<1/100\). Since \(D_0\ge3\) and \(D_j\) increases, for every \(0\le j\le a-11\),
\[
\frac32p\le y_j\le2p-3.
\]
This is the even-parent target band at level \(L\), and its unique even parent is
\[
y_{j+1}=2y_j-2p-L.
\]
There are exactly \(a-10\) such edges. At the next state, the stronger lower estimate
\[
\frac{D_{a-10}}p>\frac{67}{108}-\frac1{100}>\frac35
\]
and the upper estimate \(D_{a-10}/p<1\) give
\[
p<y_{a-10}<\frac75p<\frac32p-1
\]
because \(p>10\). This lies strictly above the level-\(L-1\) even band's upper endpoint \(p-3\) and strictly below the level-\(L\) band's lower endpoint \(3p/2-1\). Thus the chain has no even parent at its endpoint.

There are no odd parents anywhere along this chain. From (1), \(X_1\equiv3\pmod9\), so \(P_1=X_1/3\equiv1\pmod3\), and
\[
y_0=2P_1-2p-K-3\equiv1\pmod3.
\]
Because \(p\equiv1\pmod3\) and \(L=K-2\equiv0\pmod3\),
\[
y_{j+1}\equiv2y_j-2p-L\equiv1-y_j\pmod3.
\]
Hence the residues \(y_j\bmod3\) alternate between \(1\) and \(0\), never \(2\). An odd parent requires \(3\mid2y_j+5\), equivalently \(y_j\equiv2\pmod3\), so no odd parent exists, including at the terminal gap state.

We have exhausted every parent option: \(E\) has only \(h_0\); \(h_0\) has only \(y_0\); each \(y_j\) before the endpoint has only the displayed even parent; and \(y_{a-10}\) has no parent. The inverse-parent graph is a single finite chain ending at a height greater than \(p>2\), not at the blank root. Therefore \(E\notin\operatorname{ResetChain}(2)\). ∎

## Scope

This proves an infinite subfamily of rho-20, \(t=0,q=0\) candidate fatal heights is unreachable from the blank root. It does not exclude other rho-20 values of \(a,K\), other fatal-source families, or the machine's other possible halting gates. It does not prove #746 nonhalting and does not determine BB(6). The broader correction and finite parent-fan census are in [the rho-20 parent-fan dossier](../im-results/agent10-cascade/T0-RHO20-TWO-OF-THREE-LIFTS.md).
