# Machine 746: six further rho-20 phase-50 cylinders excluded from the blank-root reset cone

**Status:** paper-level arithmetic over the original-source first-reset inverse grammar. The exact grammar and its equivalence with genuine source first resets are kernel-certified in `FirstInverseComplete.lean`; strict decrease of every parent is kernel-certified in `ResetParentStrict.lean`. This extension is not yet Lean-formalized. It excludes six infinite residue classes inside the previously open (a\equiv50\pmod{54}) lift; it does not decide machine 746.

## Theorem

Let (a\ge50) be even and satisfy
$$
a\bmod486\in\{50,104,212,320,374,428\}.
$$
Set
$$
K=97\cdot2^{a-7}+48,\quad p=2^K,\quad Q=2^{K-a},\quad r=K+4-a,
$$
$$
B=(2K+7)2^r,\quad
D=\frac{B-16p+2K+1}{3},\quad
E=8p+K-D,\quad X=2E+5.
$$
Then (K+6a\equiv20\pmod{54}), so (K) is in the same (t=0,q=0) rho-20 fatal-source family as the previously studied (a\equiv14,32,46\pmod{54}) phases. Nevertheless,
$$
E\notin\operatorname{ResetChain}(2).
$$

The complete inverse-parent graph of (E) has exactly two first parents, (h_0) and (h_2). The (h_0)-branch is the previously established unique even chain of (a-10) edges ending at a leaf. For five of the six residue classes, (h_2) is itself a leaf. For (a\equiv320\pmod{486}), the (h_2)-branch has one odd parent followed by exactly four unique even-parent edges, and then ends at a leaf. Every leaf has height greater than (2).

## 1. Source grammar and common size bounds

Use the exact odd-parent grammar from `FirstInverseComplete.lean`: for (u\in\mathbb N), put (X_u=2u+5). An odd parent at exponent (t\ge0) and level (k\ge0) requires
$$
3^{t+1}\mid X_u,\qquad
P_t=\frac{2^tX_u}{3^{t+1}},\qquad
6\cdot2^k+1\le P_t\le8\cdot2^k-1,
$$
and the parent is (2P_t-8\cdot2^k-k-5). The even-parent band at level (k) is
$$
6\cdot2^k-1\le u\le8\cdot2^k-3,
$$
with parent (2u-8\cdot2^k-k).

For this family,
$$
x:=\frac{2K+7}{2^a}=\frac{97}{64}+\frac{103}{2^a}.
$$
For (a\ge50), (97/64<x<13/8), and the exact identities give
$$
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p},
\qquad
\frac Xp=\frac{21}{2}-\frac{3296}{3\cdot2^a}
                 +\frac{2K+13}{3p}.
$$
In particular,
\[
4p<E<\frac{53}{10}p<6p-1,\qquad 10.4p<X<10.6p.
\]
The sharper upper bound follows from \(x>97/64\) and \(K/p<2^{-a}\). Thus \(E\) lies strictly above the even band at level \(K-1\) and strictly below the even band at level \(K\), so it has no even parent.

2^tX/3^{t+1}), the size bounds place:
- (P_0) in the odd band at level (K-1);
- (P_1) in the gap ((2p,3p));
- (P_2) in the odd band at level (K-2);
- (P_3) in the gap ((p,3p/2));
- (P_4) in the gap ((p/2,3p/4)).

The modular certificate below gives (v_3(X)=4), except (v_3(X)=5) for (a\equiv104\pmod{486}). Hence no exponent (t\ge5) is possible. The only odd parents of (E) are therefore
$$
h_0=2X/3-4p-K-4,
\qquad
h_2=8X/27-2p-K-3.
$$

## 2. Exact modular certificate

For each class (c\in\{50,104,212,320,374,428\}), it suffices to compute (a=c,c+486,c+972). The derived residues used below have period (1458) in (a), so these three representatives cover all nine lifts modulo (4374) of each class modulo (486).

The period reduction is exact. One has $2^{1458}=2188=1+2187$ modulo $6561$, $2^{4374}=1$ modulo $6561$, and $2^{162}=1$ modulo $243$. Put $c_a=97\cdot2^{a-8}$, so $c_a=1$ modulo $3$ because $a$ is even. Under $a\mapsto a+1458$,
$$
\Delta K=4374c_a,\qquad \Delta r=1458(3c_a-1).
$$
Thus $p=2^K$ is unchanged modulo $6561$. If $U=2K+7$ and $T=2^r$, then
$$
\Delta U=2187c_a,\qquad
\Delta T=2187(3c_a-1)T
\quad (\bmod 6561).
$$
Since $r$ is even, $T\equiv1\pmod3$, and $U\equiv2\pmod3$, we get
\(\Delta B\equiv2187T(c_a+U(3c_a-1))\equiv4374\pmod{6561}\).
Therefore \(\Delta(3X)=2\Delta K-2\Delta B=0\pmod{6561}\), so $X$ modulo $2187$ is unchanged. The formula for $9X_1$ then gives $X_1$ modulo $27$ unchanged. Also $\Delta(K-a)=1458(3c_a-1)$ is divisible by $162$, so $Q$ modulo $243$, and hence $G$ modulo $9$, is unchanged. Finally the formula for $X_2$ gives $X_2$ modulo $81$ unchanged, and the derived $X_3$ and $G'$ residues are unchanged. Thus the three representatives per class are sufficient.

Here
$$
X_1=2h_0+5,\qquad X_2=2h_2+5,
$$
and, when (9\mid X_2),
$$
X_3=2h_3+5,\qquad
h_3=\frac{4X_2}{9}-\frac p2-K-1.
$$
Also
$$
G=\frac{26368Q+74K-23}{27},\qquad
G'=p+2K-3-\frac{4X_2}{9}.
$$

| (a\bmod486) | (a\bmod1458) | (X\bmod2187) | (X_1\bmod27) | (X_2\bmod81) | (X_3\bmod9) |
|---:|---:|---:|---:|---:|---:|
| 50 | 50 | 1296 | 21 | 60 | — |
| 50 | 536 | 567 | 21 | 33 | — |
| 50 | 1022 | 2025 | 21 | 6 | — |
| 104 | 104 | 1701 | 21 | 57 | — |
| 104 | 590 | 972 | 21 | 30 | — |
| 104 | 1076 | 243 | 21 | 3 | — |
| 212 | 212 | 324 | 21 | 51 | — |
| 212 | 698 | 1782 | 21 | 24 | — |
| 212 | 1184 | 1053 | 21 | 78 | — |
| 320 | 320 | 1134 | 21 | 45 | 5 |
| 320 | 806 | 405 | 21 | 18 | 8 |
| 320 | 1292 | 1863 | 21 | 72 | 2 |
| 374 | 374 | 1539 | 21 | 42 | — |
| 374 | 860 | 810 | 21 | 15 | — |
| 374 | 1346 | 81 | 21 | 69 | — |
| 428 | 428 | 1944 | 21 | 39 | — |
| 428 | 914 | 1215 | 21 | 12 | — |
| 428 | 1400 | 486 | 21 | 66 | — |

Every row also gives
$$
G\equiv1\pmod9,\qquad 4p+2K+1\equiv0\pmod3.
$$
For the (c=320) rows, it additionally gives
$$
X_2/9\equiv2\pmod3,qquad G'\equiv0\pmod3.
$$
The table is reproduced using exact BigInt arithmetic by [`phase50-six-classes-certificate.mjs`](phase50-six-classes-certificate.mjs).

Consequently:
- (v_3(X)=4) for (c=50,212,320,374,428), and (v_3(X)=5) for (c=104);
- (v_3(X_1)=1) in all six classes;
- (v_3(X_2)=1) for (c=50,104,212,374,428);
- (v_3(X_2)=2) for (c=320), with (X_3\not\equiv0\pmod3) and (G'\equiv0\pmod3).

## 3. The (h_0)-branch is a finite chain ending at a leaf

The common exact identities are
$$
\frac{h_0}{p}
=3-\frac{6592}{9\cdot2^a}-\frac{5K+10}{9p},
\qquad
\frac{X_1}{p}
=6-\frac{13184}{9\cdot2^a}-\frac{10K-25}{9p}.
$$
Thus $2p<h_0<3p-3$: indeed $3p-h_0=6592Q/9+(5K+10)/9>3$. Hence $h_0$ lies strictly between the even bands at levels $K-2$ and $K-1$, and has no even parent. Since (v_3(X_1)=1), only (t=0) is possible at (h_0); the coordinate (X_1/3) lies in the odd band at level (K-2). Its unique parent is (y_0).

Put (L=K-2) and (D_0=2p-y_0). Direct substitution gives
$$
D_0=\frac{26368Q+47K+31}{27},\qquad
D_0+L=G=\frac{26368Q+74K-23}{27}.
$$
The table gives (G\in\mathbb N) and (G\equiv1\pmod3). Also (K<2^a), (K\ge2a), and hence (Q=2^{K-a}\ge2^a>K). It follows that
$$
D_0>3,\qquad G<\frac{26442}{27}Q<1024Q.
$$
Define
$$
D_j=2^jG-L,\qquad y_j=2p-D_j.
$$
Then (D_{j+1}=2D_j+L). For (0\le j\le a-11),
$$
3<D_j<2^jG\le2^{a-11}\cdot1024Q=p/2,
$$
so
$$
3p/2<y_j<2p-3.
$$
These are precisely the even-parent band at level (L), and each has the unique even parent (y_{j+1}).

At the next index,
$$
\frac{D_{a-10}}p
=\frac{103}{108}
 +\frac{74K-23}{27648Q}
 -\frac{K-2}{2^aQ}.
$$
The two correction terms have total absolute value below (1/100), so
$$
15/16<D_{a-10}/p<1,qquad
p<y_{a-10}<17p/16.
$$
This is the gap between the even bands at levels (L-1) and (L), so the chain ends at a leaf.

There are no odd parents anywhere on this chain. Indeed,
$$
2y_j+5=A-2^{j+1}G,qquad A=4p+2K+1.
$$
The modular table gives (A\equiv0\pmod3) and (G\equiv1\pmod3), so (2y_j+5\equiv-2^{j+1}\not\equiv0\pmod3).

## 4. The (h_2)-branch

The common exact ratio is
$$
\frac{h_2}{p}
=\frac{10}{9}
 -\frac{26368}{81\cdot2^a}
 -\frac{65K+139}{81p}.
$$
For $a\ge50$, the two subtracted terms have sum below $1/9$, so $1<h_2/p<10/9$. Hence $h_2$ lies in the gap between the even bands at levels $K-3$ and $K-2$, and has no even parent.


$$
X_2=\frac{16X}{27}-4p-2K-1.
$$
Since $X_2=2h_2+5$ and $1<h_2/p<10/9$, for $p>2000$,
$$
\frac{2p}{3}<\frac{X_2}{3}
<\frac{20p}{27}+\frac53<\frac{3p}{4}.
$$
This is a gap between odd bands at levels $K-4$ and $K-3$. Therefore the $t=0$ odd parent is impossible.

### 4.1 Five residue classes: (h_2) is a leaf

For (a\bmod486\in\{50,104,212,374,428\}), the table gives (v_3(X_2)=1). Thus (t=0) is the only possible odd-parent exponent at (h_2), and its coordinate (X_2/3) lies in the displayed gap. Together with the absence of an even parent, this proves that (h_2) is a leaf.

### 4.2 The (a\equiv320\pmod{486}) class: one odd parent and a four-edge even chain

Here (v_3(X_2)=2), so only (t=0,1) can occur at (h_2). The (t=0) coordinate is in the gap above. The $t=1$ coordinate $P_1=2X_2/9$ satisfies, for $p>2000$,
$$
\frac{4p}{9}<P_1<
\left(\frac{40}{81}+\frac{10}{9p}\right)p
<\frac{99p}{200}.
$$
This is strictly inside the odd band at level $K-4$. Hence $h_2$ has exactly one odd parent,
$$
h_3=2P_1-p/2-K-1
=\frac{4X_2}{9}-\frac p2-K-1.
$$
The same bounds and $(K+1)/p<1/1000$ show
$$
\frac{19p}{50}<h_3<\frac{49p}{100},
$$
so $h_3$ lies strictly inside the even-parent band at level $K-4$. The table gives $X_3=2h_3+5\not\equiv0\pmod3$, so it has no odd parent.

Put (L'=K-4), (Delta_0=p/2-h_3), and (G'=\Delta_0+L'). Then
$$
G'=p+2K-3-\frac{4X_2}{9}.
$$
The table gives (X_2/9\equiv2\pmod3), hence (G'\equiv0\pmod3). The exact size identity is
$$
\frac{G'}p
=\frac1{81}
 +\frac{64}{243}\left(
     \frac{3296}{3\cdot2^a}
     -\frac{2K+13}{3p}
   \right)
 +\frac{702K-621}{243p}.
$$
For $a\ge50$, the bracket is positive, and
\[
0<
\frac{64}{243}\left(
     \frac{3296}{3\cdot2^a}
     -\frac{2K+13}{3p}
   \right)
 +\frac{702K-621}{243p}
<
\frac{64\cdot3296/729+702/243}{2^a}
<
\frac1{80}-\frac1{81}.
\]
Thus
\[
\frac1{82}<\frac{G'}p<\frac1{80}.
\]

Define
$
\Delta_j=2^jG'-L',\qquad
y'_j=p/2-\Delta_j.
$
Then $\Delta_{j+1}=2\Delta_j+L'$ and $L'/p<2^{-a}$. Since
$$
\Delta_0/p>1/82-2^{-a}>1/83,
$$
we have $\Delta_j>p/83>3$ for every $j\ge0$. For $0\le j\le3$,
$$
3<\Delta_j<2^j p/80\le p/10<p/8,
$$
so
$$
3p/8<y'_j<p/2-3.
$$
Each $y'_j$ is therefore in the even-parent band at level $L'$, with unique parent $y'_{j+1}$.

At \(j=4\), the lower bound improves to \(\Delta_4>p/6\) because \(16/82-2^{-a}>1/6\) for \(a\ge50\). Thus
\[
p/6<\Delta_4<p/5,
\]
and
\[
p/4<y'_4<p/3.
\]
This lies strictly between the upper endpoint \(p/4-3\) of the even band at level \(L'-1\) and the lower endpoint \(3p/8-1\) at level \(L'\). Therefore the even chain ends at \(y'_4\).

 Indeed,
$$
2y'_j+5=A'-2^{j+1}G',
\qquad A'=p+2L'+5=p+2K-3.
$$
Since $p\\equiv1\\pmod3$, $K\\equiv2\\pmod3$, and $G'\\equiv0\\pmod3$, we have $A'\\equiv2\\pmod3$, so $2y'_j+5\\equiv2\\pmod3$ for every $j$.

## 5. Exhaustion and scope

The root candidate $E$ has exactly two parents, $h_0$ and $h_2$. The $h_0$-branch ends at $y_{a-10}$. For five residue classes the $h_2$-branch ends immediately; for $a\equiv320\pmod{486}$, it follows the unique path
$$
h_2\leftarrow h_3=y'_0\leftarrow y'_1\leftarrow y'_2
\leftarrow y'_3\leftarrow y'_4,
$$
ending at a leaf. All these leaves exceed $2$. Thus no inverse-parent path from $E$ reaches the blank root, and $E\notin\operatorname{ResetChain}(2)$.

This excludes the six infinite classes
$$
a\bmod486\in\{50,104,212,320,374,428\}
$$
inside the previously open $a\equiv50\pmod{54}$ rho-20 lift. The remaining classes $a\bmod486\in\{158,266,482\}$ are not covered here. This result does not prove machine 746 nonhalting and does not determine BB(6).
