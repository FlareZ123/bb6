# Phase-50 rho-20 cylinder \(a\equiv158\pmod{3\,188\,646}\): complete root exclusion

**Status:** new paper-level infinite-family exclusion. The original reset-parent grammar and blank-root chain equivalence are source-certified elsewhere; this parameter-specific arithmetic/tree proof has not yet been Lean-compiled. It extends Agent 44's six phase-50 classes, not a machine-wide nonhalting result.

## Theorem

Let
\[
P=2\cdot3^{13}=3\,188\,646,\qquad a=158+Pn\quad(n\ge0),
\]
and set
\[
K=97\cdot2^{a-7}+48,\quad p=2^K,\quad
B=(2K+7)2^{K+4-a},
\]
\[
D=(B-16p+2K+1)/3,\qquad E=8p+K-D,\qquad X=2E+5.
\]
Then \(K\equiv2\pmod6\), \(K+6a\equiv20\pmod{54}\), and
\[
\frac{2K+7}{2^a}=\frac{97}{64}+\frac{103}{2^a}.
\]
These parameters lie in the same \(t=0,q=0\) fatal-source family as the rho-20 work in [the corrected parent-fan dossier](T0-RHO20-TWO-OF-THREE-LIFTS.md). The complete inverse-parent graph of \(E\) has no path to the blank-root value \(2\).

The source-exact inverse rules are: an even parent at level \(k\) exists precisely when
\[
6\cdot2^k-1\le u\le8\cdot2^k-3,
\quad h=2u-8\cdot2^k-k,
\]
and an odd parent is specified by \(t\ge0\), \(d=(2u+5)/3^{t+1}\) odd, and
\[
6\cdot2^k+1\le2^td\le8\cdot2^k-1,
\quad h=2^{t+1}d-8\cdot2^k-k-5.
\]
The dyadic source bands are disjoint, so each admissible \(t\) determines at most one \(k\).

## The first split and the long \(h_0\)-branch

The exact fatal-source identity gives
\[
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p},
\qquad
\frac Xp=\frac{21}{2}-\frac{3296}{3\cdot2^a}
+\frac{2K+13}{3p},
\quad x=\frac{2K+7}{2^a}.
\]
Thus \(E/p\to21/4\), strictly between the even-parent bands at levels \(K-1\) and \(K\). The modular certificate below gives \(X\bmod3^{13}=207684\), hence \(v_3(X)=4\). For \(P_t=2^tX/3^{t+1}\), the limiting ratios for \(t=0,1,2,3\) are
\[
\frac72,\quad\frac73,\quad\frac{14}{9},\quad\frac{28}{27}.
\]
Only \(t=0\) and \(t=2\) lie in odd-source bands. Consequently \(E\) has exactly two parents:
\[
h_0=\frac{2X}{3}-4p-K-4,\qquad
h_2=\frac{8X}{27}-2p-K-3.
\]

The \(h_0\)-branch is the same long even-parent chain used in Agent 44's phase-50 analysis, and the residues needed here are checked for this deeper cylinder too. The certificate gives
\[
X_1=2h_0+5\equiv21\pmod{27},\qquad
G_0\equiv1\pmod9,\qquad A_0=4p+2K+1\equiv0\pmod3.
\]
From the exact normalized formula
\[
\frac{h_0}{p}=3-\frac{6592}{9\cdot2^a}-\frac{5K+10}{9p},
\]
we have \(2p<h_0<3p-3\), so \(h_0\) has no even parent. Also
\[
\frac{X_1}{p}=6-\frac{13184}{9\cdot2^a}
-\frac{10K-25}{9p},\qquad
2p-\frac{X_1}{3}=\frac{13184Q+10K-25}{27}.
\]
The last quantity lies strictly between \(1\) and \(p/2\), placing \(X_1/3\) in the odd-source band at level \(K-2\). Since \(X_1\equiv21\pmod{27}\), \(t=0\) is the only possible odd valuation. Its parent is
\[
z_0=\frac{2X_1}{3}-2p-K-3.
\]
Thus \(h_0\) has exactly one parent, \(z_0\), at level \(K-2\). Put
\[
Q=2^{K-a},\quad
D_0=\frac{26368Q+47K+31}{27},\quad
G_0=D_0+K-2=\frac{26368Q+74K-23}{27},
\]
\[
D_j=2^jG_0-(K-2),\qquad z_j=2p-D_j.
\]
For \(0\le j\le a-11\), \(3<D_j<p/2\), so \(z_j\) lies in the even-parent band at level \(K-2\). Moreover
\[
2z_j+5=A_0-2^{j+1}G_0\not\equiv0\pmod3,
\]
so these nodes have no odd parent and their even parent is uniquely \(z_{j+1}\). At the terminal index,
\[
\frac{D_{a-10}}p=
\frac{103}{108}+\frac{74K-23}{27648Q}
-\frac{K-2}{2^aQ},
\]
which lies strictly between \(15/16\) and \(1\). Hence
\[
p<z_{a-10}<17p/16.
\]
This is an even-parent gap, and the same nonzero-modulo-three identity excludes an odd parent. The \(h_0\)-branch therefore ends at a non-root leaf.

## The \(h_2\)-branch

The second first-parent is
\[
h_2=\frac{8X}{27}-2p-K-3,\qquad
X_2=2h_2+5=\frac{16X}{27}-4p-2K-1.
\]
The certificate gives \(X_2\bmod3^{10}=45981\), so \(v_3(X_2)=3\). The possible odd-source coordinates \(2^tX_2/3^{t+1}\), for \(t=0,1,2\), have limiting ratios
\[
\frac{20}{27},\quad\frac{40}{81},\quad\frac{80}{243}.
\]
The first and third are in dyadic gaps; the middle is in the odd-source band at level \(K-4\). Also \(h_2/p\to10/9\), an even-parent gap. Thus \(h_2\) has exactly one parent,
\[
h_3=\frac{4X_2}{9}-\frac p2-K-1.
\]
Its odd numerator is
\[
X_3=2h_3+5=\frac{8X_2}{9}-p-2K+3
\equiv679\pmod{3^8},
\]
so it has no odd parent. Its unique even parent is \(y_1\), in the band at level \(K-4\).

Write
\[
A_1=p+2K-3,\qquad
G_1=A_1-\frac{4X_2}{9},\qquad
y_j=\frac p2-\bigl(2^jG_1-(K-4)\bigr).
\]
Then \(y_0=h_3\) and \(y_{j+1}=2y_j-p/2-K+4\). The limiting heights are
\[
\frac{y_j}{p}\longrightarrow
\frac12-\frac{2^j}{81}
\quad(j=0,1,2,3,4).
\]
The first four values \(79/162,77/162,73/162,65/162\) lie in the even band at level \(K-4\); \(49/162\), the terminal \(y_4/p\), lies in the gap between the \(K-5\) and \(K-4\) bands.

For \(Z_j=2y_j+5=A_1-2^{j+1}G_1\), the certificate gives
\[
(Z_0,Z_1,Z_2,Z_3,Z_4)\equiv(31,45,73,48,79)\pmod{81}.
\]
Thus \(y_0,y_2,y_4\) have no odd parent. At \(y_3\), \(v_3(Z_3)=1\), but \(Z_3/(3p)\to65/243\) is in a gap, so \(y_3\) has no odd parent either. At \(y_1\), \(v_3(Z_1)=2\): its \(t=0\) coordinate has limit \(77/243\), in a gap, while its \(t=1\) coordinate has limit \(154/729\), in the band at level \(K-5\). Therefore \(y_1\) has exactly two parents: its even parent \(y_2\) and the odd parent
\[
h_5=\frac{4Z_1}{9}-\frac p4-K.
\]
The even chain \(y_2\to y_3\to y_4\) ends at the leaf \(y_4\).

## Closing the additional \(h_5\)-branch

The successive odd numerators and parent formulas are
\[
\begin{aligned}
X_5&=2h_5+5=\frac{8Z_1}{9}-\frac p2-2K+5,\\
h_6&=\frac{2X_5}{3}-\frac p8-K+1,\\
X_6&=2h_6+5=\frac{4X_5}{3}-\frac p4-2K+7,\\
h_7&=2h_6-\frac p8-K+6,\\
X_7&=2h_7+5=\frac{8X_5}{3}-\frac{3p}{4}-6K+21,\\
h_8&=\frac{2X_7}{3}-\frac p{16}-K+2,\\
X_8&=2h_8+5=\frac{4X_7}{3}-\frac p8-2K+9,\\
h_9&=2h_8-\frac p{16}-K+7,\\
X_9&=2h_9+5=2X_8-\frac p8-2K+9,\\
h_{10}&=\frac{2X_9}{3}-\frac p{32}-K+3,\\
X_{10}&=2h_{10}+5=\frac{4X_9}{3}-\frac p{16}-2K+11.
\end{aligned}
\]
The exact modular residues are
\[
\begin{array}{c|c|c}
\text{numerator}&\text{residue}&v_3\\ \hline
X_5&693\pmod{3^6}&2\\
X_6&212\pmod{3^5}&0\\
X_7&36\pmod{3^4}&2\\
X_8&18\pmod{3^3}&2\\
X_9&6\pmod{3^2}&1\\
X_{10}&2\pmod3&0.
\end{array}
\]
The corresponding limiting heights are
\[
\begin{array}{c|c}
\text{node}&\text{height}/p\text{ limit}\\ \hline
h_5&503/2916\\
h_6&1837/17496\\
h_7&1487/17496\\
h_8&5335/104976\\
h_9&4109/104976\\
h_{10}&13189/629856.
\end{array}
\]
Here \(h_5\) is in an even-parent gap. Its \(t=0\) odd coordinate has limit \(503/4374\), in the band at level \(K-6\); its \(t=1\) coordinate \(1006/13122\) is in a gap. Hence its only parent is \(h_6\). The node \(h_6\) has no odd parent and has the unique even parent \(h_7\). The node \(h_7\) is in an even-parent gap; its \(t=0\) coordinate \(1487/26244\) is in the band at level \(K-7\), while its \(t=1\) coordinate \(2974/78732\) is in a gap. Its only parent is \(h_8\). The node \(h_8\) has an even parent \(h_9\); its two possible odd coordinates have limits
\[
\frac{5335}{157464},\qquad\frac{10670}{472392},
\]
both in gaps. The node \(h_9\) is in an even-parent gap and has \(v_3(X_9)=1\); its sole odd coordinate \(4109/157464\) is in the band at level \(K-8\), giving parent \(h_{10}\). Finally \(h_{10}\) is in an even-parent gap and \(X_{10}\not\equiv0\pmod3\), so it is a leaf.

Combining the two \(h_2\)-subbranches, every path ends at either \(y_4\) or \(h_{10}\), both much larger than \(2\). The complete parent graph is therefore
\[
E\to h_0\to z_0\to\cdots\to z_{a-10},
\qquad
E\to h_2\to h_3\to y_1
\begin{cases}
\to y_2\to y_3\to y_4,\\
\to h_5\to h_6\to h_7\to h_8\to h_9\to h_{10}.
\end{cases}
\]
Every displayed parent set is exhaustive by the valuation bounds and disjoint source bands. No branch reaches \(2\). By the source-certified equivalence between blank-root ResetChain membership and original-machine reset-parent ancestry, this \(E\) is not in the blank-root chain.

## Period and exact modular certificate

Set \(M=3^{14}=4\,782\,969\). The period is \(P=2\cdot3^{13}\), and
\[
2^P\equiv1\pmod M.
\]
Under \(a\mapsto a+P\), the change in \(K\) is
\[
97\cdot2^{a-7}(2^P-1),
\]
which is divisible by \(2\cdot3^{14}=3P\), since \(a-7\ge1\). Thus \(K\) is unchanged modulo \(M\) and modulo the exponent period \(P\); \(2^K\), \(2^{K+4-a}\), and \(2^{K-a}\) are unchanged in the moduli used above. All listed residues therefore hold for every \(a\equiv158\pmod P\), not merely for \(a=158\). Also \(P/486=6561\), so the cylinder is contained in \(a\equiv158\pmod{486}\). Since \(P\) is divisible by \(18\), the eventual period-18 law for \(2^m\bmod54\) shows \(K\bmod54=44\) and \(K+6a\bmod54=20\) throughout the cylinder.

The complete exact-integer reproducer is [phase50_158_chain_certificate.mjs](phase50_158_chain_certificate.mjs). It checks the period, the modular divisions, all residues above, and agreement at \(a=158,158+P,158+2P\).

For the fixed-depth tree, all limiting band/gap comparisons are strict. The smallest odd-source margin is
\[
\frac3{128}-\frac{10670}{472392}
=\frac{51416}{60466176}>\frac1{1200}.
\]
Every normalized height is affine in \(x\) and \(K/p\). Along the finite \(h_2\)-tree, an even-parent step multiplies the preceding error by \(2\), and an odd-parent step multiplies it by \(2^{t+2}/3^{t+1}<2\); the longest branch has nine edges. Using \(x-97/64=103/2^a\), \(K/p<2^{-a}\), and \(1/p<2^{-a}\), a deliberately crude induction bounds every displayed ratio's deviation from its limit by \(2^{36}2^{-a}\le2^{-14}<1/1200\). Thus none of the strict band/gap decisions can change for \(a\ge158\); the integer endpoint offsets \(1\) and \(3\) are also absorbed because \(p/1200>3\).

## Scope and next work

This removes one infinite cylinder from the phase-50 rho-20 lift. Together with Agent 44's six full classes \(a\bmod486\in\{50,104,212,320,374,428\}\), it narrows that lift, but does not settle it: the \(266\) and \(482\) classes modulo \(486\), and the other \(6560\) cylinders inside the \(158\) class modulo \(P\), remain open. The \(a\bmod54=10,28\) lifts, the residual \(a\bmod18=2\) class, other #746 fatal branches, and BB(6) remain open. This note is intermediate research, not a Lean-certified result.
