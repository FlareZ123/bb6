# Machine 746: three further rho-20 phase families excluded from the blank-root reset cone

**Status.** This is a paper-level arithmetic theorem over the original-source first-reset inverse grammar. The exact grammar and its equivalence with genuine source first resets are kernel-certified in [FirstInverseComplete.lean](../im-results/agent10-cascade/FirstInverseComplete.lean); strict decrease of every parent is kernel-certified in [ResetParentStrict.lean](../im-results/agent10-cascade/ResetParentStrict.lean). The arithmetic specialization below is not yet Lean-formalized. It excludes two complete lifts of the residual (a\equiv14\pmod{18}) class and one lift of (a\equiv10\pmod{18}), not the whole machine.

## Theorem

Let (a\ge32) be even and satisfy
[
a\equiv14,\ 32,\text{ or }46\pmod{54}.
]
Put
[
K=97\cdot2^{a-7}+48,\qquad
p=2^K,\qquad Q=2^{K-a},\qquad r=K+4-a,
]
[
B=(2K+7)2^r,\qquad
D=\frac{B-16p+2K+1}{3},\qquad
E=8p+K-D.
]
Then (K+6a\equiv20\pmod{54}), so (E) is the corresponding (t=0,q=0) rho-20 fatal-source candidate. Nevertheless,
[
E\notin\operatorname{ResetChain}(2).
]

More precisely, the complete inverse-parent graph of (E) has exactly two first parents. One is a leaf. The other has a unique parent chain of (a-10) even edges, ending at a leaf. Neither branch reaches the blank-tape root.

## 1. Exact arithmetic and the modular certificate

Since (a\equiv14) or (32\pmod{54}), (a) is even. Also
[
2K+7=97\cdot2^{a-6}+103,qquad
x:=\frac{2K+7}{2^a}=\frac{97}{64}+\frac{103}{2^a}.
]
For (a\ge32),
[
\frac{97}{64}<x<\frac{13}{8},\qquad
\frac Bp=16x.
]
The defining numerator of (D) is divisible by three: (K\equiv2\pmod3), (p\equiv1\pmod3), (r) is even, and hence (B\equiv2\pmod3). Thus (D\in\mathbb N).

Set
[
X=2E+5,\qquad h_0=\frac{2X}{3}-4p-K-4,qquad X_1=2h_0+5,
]
and
[
A=4p+2K+1,qquad
G=\frac{26368Q+74K-23}{27}.
]
The exact identities used below are
[
3X=80p+2K+13-2B,\
9X_1=248p-8B-10K+25,\
2y_0+5=A-2G,
]
where (y_0) is defined in Section 3. Direct substitution also gives
[
h_2=\frac{8X}{27}-2p-K-3,qquad
2h_2+5=\frac{16X}{27}-4p-2K-1.
]

The modular table below is exact. The row parameter is (a\bmod162); (K_{243}) denotes (K\bmod243), and similarly for the other columns. Define (G_{\rm num}=26368Q+74K-23).

| (a\bmod54) | (a\bmod162) | (K_{243}) | (K_{162}) | (r_{162}) | (p_{243}) | (Q_{243}) | (2^r_{243}) | (B_{243}) | (3X_{243}) | (9X_{1,243}) | (A_9) | (G_{\rm num,243}) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 14 | 14  | 71  | 152 | 142 | 229 | 73  | 196 | 44  | 162 | 108 | 6 | 189 |
| 14 | 68  | 233 | 152 | 88  | 229 | 235 | 115 | 206 | 162 | 108 | 6 | 189 |
| 14 | 122 | 152 | 152 | 34  | 229 | 154 | 34  | 125 | 162 | 108 | 6 | 189 |
| 32 | 32  | 44  | 44  | 16  | 67  | 208 | 169 | 17  | 81  | 27  | 6 | 108 |
| 32 | 86  | 206 | 44  | 124 | 67  | 127 | 88  | 179 | 81  | 27  | 6 | 108 |
| 32 | 140 | 125 | 44  | 70  | 67  | 46  | 7   | 98  | 81  | 27  | 6 | 108 |\n| 46 | 46  | 122 | 122 | 80  | 22  | 205 | 121 | 239 | 81  | 162 | 0 | 162 |\n| 46 | 100 | 41  | 122 | 26  | 22  | 124 | 40  | 158 | 81  | 162 | 0 | 162 |\n| 46 | 154 | 203 | 122 | 134 | 22  | 43  | 202 | 77  | 81  | 162 | 0 | 162 |

Here (3X_{243}) means (3X\bmod243), and likewise for (9X_{1,243}). Consequently,
[
X\bmod81=
\begin{cases}
54,&a\equiv14\pmod{54},\\
27,&a\equiv32\text{ or }46\pmod{54},
\end{cases}
\qquad
X_1\bmod27=
\begin{cases}
12,&a\equiv14\pmod{54},\\
3,&a\equiv32\pmod{54},\\
18,&a\equiv46\pmod{54},
\end{cases}
]
Thus
[
v_3(X)=3,\qquad
v_3(X_1)=
\begin{cases}
1,&a\equiv14,32\pmod{54},\\
2,&a\equiv46\pmod{54}.
\end{cases}
]
The table also gives
[
A\equiv
\begin{cases}
6\pmod9,&a\equiv14,32\pmod{54},\\
0\pmod9,&a\equiv46\pmod{54},
\end{cases}
\qquad
G\equiv
\begin{cases}
7\pmod9,&a\equiv14\pmod{54},\\
4\pmod9,&a\equiv32\pmod{54},\\
6\pmod9,&a\equiv46\pmod{54},
\end{cases}
]
and
[
\frac X{27}\equiv
\begin{cases}
2\pmod3,&a\equiv14\pmod{54},\\
1\pmod3,&a\equiv32,46\pmod{54}.
\end{cases} \tag{2}
]
In all three phases (p\equiv1\pmod3) and (K\equiv2\pmod3). In phases 14 and 32, (A\equiv0\pmod3) and (G\equiv1\pmod3); in phase 46, (A\equiv0\pmod9) and (G\equiv6\pmod9).

**Why the table covers every lift.** Modulo (243), (2^{162}\equiv1); modulo (162), (2^{54}\equiv82) and (82^2\equiv82). For phase (14), (2^7\equiv128\pmod{162}) and (128\cdot82\equiv128); for phase (32), (2^{25}\equiv20\pmod{162}) and (20\cdot82\equiv20); for phase (46), (2^{39}\equiv116\pmod{162}) and (116\cdot82\equiv116). Hence (K\equiv152,44,122\pmod{162}) respectively throughout the three phases. The residue (a\bmod162) has the three displayed values in each phase, and the period (162) modulo (243) then gives exactly the nine rows. All remaining columns follow by the displayed defining formulas. The nine-row calculation is independently reproducible with [rho20-14-32-46-modular-certificate.mjs](../im-results/agent10-cascade/rho20-14-32-46-modular-certificate.mjs).

## 2. The root has exactly two parents

The original-source odd-parent grammar is: for (u\in\mathbb N), put (X_u=2u+5); an odd parent at exponent (t\ge0) and level (k\ge0) requires
[
3^{t+1}\mid X_u,qquad
P_t=\frac{2^tX_u}{3^{t+1}},qquad
6\cdot2^k+1\le P_t\le8\cdot2^k-1,
]
and the parent is (2P_t-8\cdot2^k-k-5). The even-parent band at level (k) is
[
6\cdot2^k-1\le u\le8\cdot2^k-3,
]
with parent (2u-8\cdot2^k-k). These are the exact source ResetParent cases, not a maximal-valuation approximation.

First,
[
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p}.
]
The bounds on (x), together with (K<p), give (4p<E<6p). This is the gap between the even-parent bands at levels (K-1) and (K), so (E) has no even parent.

The first identity gives
[
\frac Xp=\frac{21}{2}-\frac{3296}{3\cdot2^a}
+\frac{2K+13}{3p}.
]
For (a\ge32), the two corrections have absolute value below (1/1000); in particular
[
10.4<\frac Xp<10.6.
]
Therefore
[
3p< P_0:=X/3<4p,qquad
2p<P_1^{(E)}:=2X/9<3p,qquad
\frac32p<P_2:=4X/27<2p.
]
By (1), only (t=0,1,2) can occur at (E). The (t=1) coordinate lies in the gap ((2p,3p)); (P_0) is in the odd-source band at level (K-1), and (P_2) is in the odd-source band at level (K-2). Thus the only odd parents are
[
h_0=2P_0-4p-K-4
\quad\text{and}\quad
h_2=2P_2-2p-K-3.
]

The first has the exact expression
[
h_0=3p-\frac{6592}{9\cdot2^a}p-\frac{5K+10}{9}.
]
For (a\ge32), this gives (2p<h_0<3p). Also (h_0) is even. The adjacent even-parent bands end at (2p-3) and begin at (3p-1); hence (h_0) has no even parent. Its odd numerator is (X_1=2h_0+5). In phases 14 and 32, (v_3(X_1)=1), so only (t=0) is possible. In phase 46, (v_3(X_1)=2), so (t=1) is the only additional possibility; its source coordinate satisfies
[
\frac{2X_1}{9p}\in(10/9,4/3),
]
which lies in the gap ((p,3p/2)). Thus only (t=0) is possible in every phase. Moreover,

For the second parent,
[
\frac{h_2}{p}
=\frac{10}{9}-\frac{26368}{81\cdot2^a}
-\frac{65K+139}{81p}.
]
For (a\ge32), this lies strictly between (1) and (10/9), hence (p<h_2<3p/2-1), the gap between the even-parent bands at levels (K-3) and (K-2). Its odd numerator satisfies
[
2h_2+5=\frac{16X}{27}-4p-2K-1.
]
By (2), this is congruent to (2\pmod3) in phase (14) and (1\pmod3) in phases (32) and (46). It has no odd parent either. Therefore (h_2) is a leaf.

## 3. The (h_0)-branch is a finite even chain ending at a leaf

Put (L=K-2) and (D_0=2p-y_0). Direct substitution gives
[
D_0=\frac{26368Q+47K+31}{27},\qquad
G:=D_0+L=\frac{26368Q+74K-23}{27}. \tag{3}
]
The modular table proves (G\in\mathbb N) and (G\equiv1\pmod3). Define
[
D_j=2^jG-L,\qquad y_j=2p-D_j.
]
Then
[
D_{j+1}=2D_j+L,qquad
y_{j+1}=2y_j-2p-L,
]
and
[
\frac{D_j}{p}
=\frac{26368}{27\cdot2^{a-j}}
+\frac{2^j(74K-23)}{27p}-\frac Lp. \tag{4}
]

We have (K<2^a) and (K\ge2a), so (Q=2^{K-a}\ge2^a>K). From (3),
[
D_0>3,qquad
G<\frac{26368+74}{27}q<1024q.
]
Since (D_{j+1}=2D_j+L) with (L>0), (D_j\ge D_0>3). For (0\le j\le a-11),
[
D_j<2^jG\le2^{a-11}\cdot1024q=\frac p2.
]
Consequently
[
\frac32p\le y_j\le2p-3
\qquad(0\le j\le a-11).
]
This is exactly the even-parent band at level (L). The preceding band's upper endpoint is (p-3), and the following band's lower endpoint is (3p-1), so this parent is unique and is (y_{j+1}).

At the next index, (4) gives
[
\frac{D_{a-10}}p
=\frac{103}{108}
+\frac{74K-23}{27648q}
-\frac{K-2}{2^a q}.
]
Both correction terms have absolute value below (1/100), using (Q>K) and (a\ge32). Since
[
\frac{103}{108}-\frac1{100}>\frac{15}{16},
\qquad
\frac{103}{108}+\frac1{100}<1,
]
we obtain
[
\frac{15}{16}<\frac{D_{a-10}}p<1,
\qquad
p<y_{a-10}<\frac{17}{16}p.
]
This lies strictly above the level-((L-1)) even band's upper endpoint (p-3) and strictly below the level-(L) band's lower endpoint (3p/2-1). Thus (y_{a-10}) has no even parent.

There are no odd parents at any (y_j), including the terminal state, but the reason depends on the phase. In phases 14 and 32, (A\equiv0\pmod3) and (G\equiv1\pmod3), so
[
2y_j+5=A-2^{j+1}G\equiv-2^{j+1}\not\equiv0\pmod3.
]
In phase 46, (A\equiv0\pmod9) and (G\equiv6\pmod9), so
[
2y_j+5\equiv-6\cdot2^{j+1}\pmod9
]
is always 3 or 6 modulo 9. Thus (v_3(2y_j+5)=1), and only (t=0) can be considered. For (j\le a-11), the established band (3p/2\le y_j\le2p-3) gives
[
p<\frac{2y_j+5}{3}<\frac43p,
]
which lies in the gap between the odd-source bands at levels (K-3) and (K-2). At the terminal state, (p<y_{a-10}<17p/16) gives
[
\frac23p<\frac{2y_{a-10}+5}{3}<\frac34p,
]
the gap between the odd-source bands at levels (K-4) and (K-3). Hence phase 46 also has no odd parent anywhere on the chain.

We have now exhausted the entire parent graph:
[
E\longleftarrow\{h_0,h_2\},\qquad
h_2\text{ is a leaf},\qquad
h_0\longleftarrow y_0\longleftarrow y_1\longleftarrow\cdots
\longleftarrow y_{a-10},
]
where every arrow after (h_0\leftarrow y_0) is the unique even parent, and (y_{a-10}) is a leaf. All these heights are greater than (p>2). Thus no inverse-parent path from (E) reaches (2), proving the theorem. ∎

## Scope and remaining work

This removes the (a\equiv14,32\pmod{54}) lifts of the residual (a\equiv14\pmod{18}) class and the (a\equiv46\pmod{54}) lift of the residual (a\equiv10\pmod{18}) class. The (a\equiv50\pmod{54}) lift, the (a\equiv10,28\pmod{54}) lifts, the residual (a\equiv2\pmod{18}) class, other fatal-source families, and other #746 halting gates remain open. This result does not prove #746 nonhalting and does not determine BB(6).
