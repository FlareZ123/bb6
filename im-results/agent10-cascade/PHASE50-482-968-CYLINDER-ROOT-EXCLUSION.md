# Phase-50 rho-20 cylinder \(a\equiv968\pmod{3\,188\,646}\): complete root exclusion

**Status:** a second paper-level infinite-family exclusion inside the phase-50 rho-20 lift. The reset-parent grammar and blank-root chain equivalence are source-certified elsewhere; this parameter-specific parent-tree proof has not yet been Lean-compiled. It is independent of the deeper \(a\equiv158\pmod P\) cylinder, although both use the same period \(P=2\cdot3^{13}\).

## Theorem and initial fork

Let
\[
P=2\cdot3^{13}=3\,188\,646,\qquad a=968+Pn\quad(n\ge0),
\]
and define
\[
K=97\cdot2^{a-7}+48,\quad p=2^K,\quad
B=(2K+7)2^{K+4-a},
\]
\[
D=(B-16p+2K+1)/3,\qquad E=8p+K-D,\qquad X=2E+5.
\]
Then \(a\equiv482\pmod{486}\), \(K\equiv2\pmod6\), and \(K+6a\equiv20\pmod{54}\). Also
\[
\frac{2K+7}{2^a}=\frac{97}{64}+\frac{103}{2^a}.
\]
Thus this is another infinite cylinder in the same \(t=0,q=0\) fatal-source family.

As in the 158-cylinder proof,
\[
\frac Ep\longrightarrow\frac{21}{4},\qquad
\frac Xp\longrightarrow\frac{21}{2}.
\]
The certificate gives \(X\bmod3^{13}=141588\), so \(v_3(X)=4\). The four possible odd-source coordinates have limits \(7/2,7/3,14/9,28/27\); exactly \(t=0,2\) are in bands. There is no even parent of \(E\). Its complete first-parent set is
\[
h_0=\frac{2X}{3}-4p-K-4,\qquad
h_2=\frac{8X}{27}-2p-K-3.
\]

The \(h_0\)-branch is exactly the long even chain already used in the 158-cylinder note. Here the same residues are certified:
\[
X_1=2h_0+5\equiv21\pmod{27},\quad
G_0\equiv1\pmod9,\quad A_0=4p+2K+1\equiv0\pmod3.
\]
The explicit formulas and terminal-gap proof are given in that note; they apply unchanged to this cylinder.

## The \(h_2\)-branch and its even spine

Set
\[
X_2=2h_2+5=\frac{16X}{27}-4p-2K-1.
\]
The exact residue \(X_2\bmod3^{10}=18720\) gives \(v_3(X_2)=2\). Its possible odd-source coordinates have limits
\[
\frac{20}{27}\quad(t=0),\qquad
\frac{40}{81}\quad(t=1).
\]
The first is in a gap and the second is in the band at level \(K-4\). Also \(h_2/p\to10/9\), an even-parent gap. Thus \(h_2\) has exactly one parent,
\[
h_3=\frac{4X_2}{9}-\frac p2-K-1.
\]
Now
\[
X_3=2h_3+5=\frac{8X_2}{9}-p-2K+3
\equiv5850\pmod{3^8},
\]
so \(v_3(X_3)=2\). The \(t=0\) coordinate has limit \(79/243\), in a gap; the \(t=1\) coordinate has limit \(158/729\), in the band at level \(K-5\). Hence \(h_3\) has an odd parent \(c_0\), as well as its even parent \(y_1\):
\[
c_0=\frac{4X_3}{9}-\frac p4-K.
\]

For the even spine, put
\[
A_1=p+2K-3,\qquad G_1=A_1-\frac{4X_2}{9},\qquad
y_j=\frac p2-\bigl(2^jG_1-(K-4)\bigr).
\]
Then \(y_0=h_3\) and \(y_{j+1}=2y_j-p/2-K+4\). The limiting heights are
\[
\frac{y_j}{p}\longrightarrow\frac12-\frac{2^j}{81}
\quad(j=0,1,2,3,4).
\]
The first four values \(79/162,77/162,73/162,65/162\) lie in the even band at level \(K-4\); \(49/162\), the terminal \(y_4/p\), is in the gap between the \(K-5\) and \(K-4\) bands.

For \(Z_j=2y_j+5=A_1-2^{j+1}G_1\), the certificate gives
\[
(Z_0,Z_1,Z_2,Z_3,Z_4)
\equiv(5850,910,4152,4075,3921)\pmod{3^8}.
\]
Thus \(y_1,y_3\) have no odd parent. At \(y_2\), \(v_3(Z_2)=1\), but \(Z_2/(3p)\to73/243\) is in a gap. At \(y_4\), \(v_3(Z_4)=1\) and \(Z_4/(3p)\to49/243\), in the band at level \(K-5\). Therefore \(y_4\) has the additional odd parent
\[
b_6=\frac{2Z_4}{3}-\frac p4-K.
\]
The node \(b_6\) has height limit \(149/972\), an even-parent gap, and its odd numerator satisfies
\[
2b_6+5\equiv589\pmod{3^6},
\]
so it has no odd parent. It is a leaf.

## Closing the \(c_0\)-branch

The odd numerator of \(c_0\) is
\[
W_0=2c_0+5=\frac{8X_3}{9}-\frac p2-2K+5
\equiv561\pmod{3^6},
\]
so \(v_3(W_0)=1\). The height \(c_0/p\to535/2916\) lies in an even-parent gap. Its only odd coordinate is \(W_0/3\), with limit \(535/4374\), in the band at level \(K-6\). Thus its only parent is
\[
c_1=\frac{2W_0}{3}-\frac p8-K+1.
\]
The height \(c_1/p\to2093/17496\) is in the even band at level \(K-6\). Its odd numerator satisfies
\[
W_1=2c_1+5\equiv36\pmod{3^5},
\]
so \(v_3(W_1)=2\). Its \(t=0\) coordinate has limit \(2093/26244\), in a gap; its \(t=1\) coordinate has limit \(4186/78732\), in the band at level \(K-7\). Hence \(c_1\) has two parents: its even parent \(c_2\) and the odd parent
\[
c_5=\frac{4W_1}{9}-\frac p{16}-K+2.
\]
The height limit \(c_5/p=13805/314928\) lies in an even-parent gap, and
\[
2c_5+5\equiv2\pmod3.
\]
Thus \(c_5\) is a leaf.

The even branch is
\[
c_2=2c_1-\frac p8-K+6,\qquad
c_3=2c_2-\frac p8-K+6,\qquad
c_4=2c_3-\frac p8-K+6.
\]
Their limiting heights are
\[
\frac{c_2}{p}\to\frac{1999}{17496},\quad
\frac{c_3}{p}\to\frac{1811}{17496},\quad
\frac{c_4}{p}\to\frac{1435}{17496}.
\]
The first two lie in the even band at level \(K-6\); \(c_4/p\) is in the gap between the \(K-7\) and \(K-6\) bands. Their odd numerators have exact residues
\[
2c_2+5\equiv8\pmod{3^4},\quad
2c_3+5\equiv6\pmod{3^3},\quad
2c_4+5\equiv2\pmod{3^2}.
\]
The first and last are nonzero modulo \(3\). The middle has valuation one, but its only odd coordinate has limit \(1811/26244\), in the gap between the \(K-7\) and \(K-6\) bands. Therefore \(c_2\) has only its even parent \(c_3\), \(c_3\) has only its even parent \(c_4\), and \(c_4\) is a leaf.

Combining the branches, the complete parent graph is
\[
E\to h_0\to z_0\to\cdots\to z_{a-10},
\]
and
\[
E\to h_2\to h_3
\begin{cases}
\to y_1\to y_2\to y_3\to y_4\to b_6,\\
\to c_0\to c_1
  \begin{cases}
  \to c_2\to c_3\to c_4,\\
  \to c_5.
  \end{cases}
\end{cases}
\]
Every parent set is exhaustive by the displayed valuations and disjoint dyadic source bands. All terminal nodes are non-root leaves. Hence \(E\) is not in the blank-root reset-parent ancestry.

## Period and exact certificate

Take \(M=3^{14}=4\,782\,969\) and \(P=2\cdot3^{13}\). Since \(2^P\equiv1\pmod M\), the change in \(K\) under \(a\mapsto a+P\) is
\[
97\cdot2^{a-7}(2^P-1),
\]
a multiple of \(2\cdot3^{14}=3P\). Therefore all residues used above are periodic with period \(P\). Also \(P/486=6561\), so \(a\equiv968\pmod P\) implies \(a\equiv482\pmod{486}\). The period-18 law for \(2^m\bmod54\) gives \(K\bmod54=44\) and \(K+6a\bmod54=20\) throughout the cylinder.

The exact BigInt reproducer is [phase50_482_968_chain_certificate.mjs](phase50_482_968_chain_certificate.mjs). It checks the modular divisions, the listed residues, and agreement at \(a=968,968+P,968+2P\).

All limiting band/gap comparisons in the finite \(h_2\)-tree are strict. The smallest listed margin is \(1/8-535/4374=47/17496>1/1200\). The finite tree has fewer than nine parent edges; using \(x-97/64=103/2^a\), \(K/p<2^{-a}\), and \(1/p<2^{-a}\), the same crude affine-error induction as in the 158-cylinder proof bounds every normalized ratio's deviation by \(2^{36}2^{-a}\le2^{-14}<1/1200\). The integer endpoint offsets are therefore harmless.

## Scope

This excludes one infinite cylinder inside \(a\bmod486=482\), not the whole class. Together with Agent 44's six full mod-486 classes and the \(a\equiv158\pmod P\) result, it narrows the phase-50 lift further. The \(a\bmod486=266\) class, the other 6560 cylinders inside each of the 158 and 482 classes modulo \(P\), all other phase-50 classes, the \(a\bmod54=10,28\) lifts, the residual \(a\bmod18=2\) class, other #746 fatal branches, and BB(6) remain open. This is intermediate paper-level research, not a Lean-certified result.
