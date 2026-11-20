# Rho-20 residual class 2: dyadic terminal-window root exclusions in a≡38 mod54

**Status.** The (m=0) chain below is an exact arithmetic derivation at the already source-verified `ResetParent` grammar level. The shifted dyadic terminal-window theorem added below extends it to at least (a-21) further (K)-values for every (a\equiv38\pmod{54}), with an exact count of 233,015 shifted values already at (a=38). Both arguments are paper-level and have **not yet been compiled in Lean**. Keep them in `im-results/` pending source-level formalization and adversarial review.

These results resolve additional infinite subfamilies inside the residual (a\bmod18=2) class identified in [Agent 10's rho-20 analysis](../agent10-cascade/T0-RHO20-TWO-OF-THREE-LIFTS.md). They do not settle the other two (a\bmod54) phases, the whole #746 family, or BB(6).

## Baseline family (m=0)

For every
[
a=38+54n\quad(n\ge0),\qquad
K=97\cdot2^{a-7}+48,
]
put
[
p=2^K,\quad q=2^{K-a},\quad r=K+4-a,\quad
B=(2K+7)2^r,
]
[
D=(B-16p+2K+1)/3,\qquad E=8p+K-D.
]
The intended conclusion is
[
\neg\,\operatorname{ResetChain}(2,E).
]
Here `ResetChain` and `ResetParent` are the exact source-C first-reset grammar in `im-results/agent10-cascade/ResetChain.lean` and `FirstInverseComplete.lean`; in particular, no bounded valuation cutoff is being introduced.

The proof identifies the complete inverse-parent tree of (E): it is a single chain ending at a non-root state with no parent.

## Initial two odd edges

Let (X=2E+5). Direct substitution gives
[
3X=80p+2K+13-2B,
\qquad
X/p=21/2-3296/(3\cdot2^a)+(2K+13)/(3p).
]
For the first odd parent define
[
h=2X/3-4p-K-4.
]
Then (\operatorname{ResetParent}(h,E)) is the (t=0,k=K-1) odd edge.

The next numerator (X_1=2h+5) satisfies
[
9X_1=248p-8B-10K+25,
\qquad
X_1/p=6-13184/(9\cdot2^a)-(10K-25)/(9p).
]
Define
[
y_0=2X_1/3-2p-K-3.
]
Then (\operatorname{ResetParent}(y_0,h)) is the (t=0,k=K-2) odd edge.

For (a\ge38), (K=97\cdot2^{a-7}+48) gives (K<2^a\le q), so (q>K). The displayed ratio identities yield the useful strict bounds
[
28/3<X/p<21/2,\
4<E/p<6,\
59/10<X_1/p<6,\
2p<h<3p-1.
]
The first two inequalities put (E) in the even-parent gap ((4p,6p)). Since (X\equiv18\pmod{27}), its only possible odd exponents are (t=0,1): (X/3\in(3p,4p)) is in the (k=K-1) source band, while (2X/9\in(2p,3p)) is in a gap. Thus (h) is the unique parent of (E).

Likewise (X_1\equiv9\pmod{27}), so only (t=0,1) are possible at (h). Here (X_1/3\in(3p/2,2p)) is in the (k=K-2) source band, while (2X_1/9\in(p,3p/2)) is in a gap. The bound on (h) excludes even parents. Thus (y_0) is the unique parent of (h).

The exact congruences (X\equiv18\pmod{27}) and (X_1\equiv9\pmod{27}) are established below.

## The same-level even chain

Set
[
L=K-2,\
D_0=2p-y_0,\
G=D_0+L.
]
Algebra gives the particularly useful closed forms
[
D_0=(26368q+47K+31)/27,\
G=(26368q+74K-23)/27.
]
For (j\ge0), define
[
D_j=2^jG-L,\
y_j=2p-D_j.
]
Then (y_0) agrees with the initial parent above, and
[
y_{j+1}=2y_j-2p-L.
]
Consequently (\operatorname{ResetParent}(y_{j+1},y_j)) is the even edge at level (k=L=K-2) whenever
[
3p/2\le y_j\le2p-3.
]

Since (q>K),
[
G<1024q,\
D_0>3.
]
For every (0\le j\le a-11),
[
3\le D_j<2^jG\le2^{a-11}\cdot1024q=p/2,
]
hence
[
3p/2\le y_j\le2p-3.
]
Thus all (a-10) same-level even-parent edges exist.

The crucial new observation is the exact numerator formula
[
X_j:=2y_j+5=A-2^{j+1}G,
\qquad A:=4p+2K+1.
]
For the chosen congruence class, (A\equiv6\pmod9) and (G\equiv0\pmod9). Therefore
[
X_j\equiv6\pmod9
\quad\text{for every }j\ge0.
]
Every (X_j) has 3-adic valuation exactly one. In particular, the only possible odd-parent exponent is (t=0).

For (j\le a-11), the corresponding odd source coordinate is
[
X_j/3=(2y_j+5)/3\in(p,4p/3),
]
which lies strictly between the adjacent source bands ([3p/4+1,p-1]) and ([3p/2+1,2p-1]). Hence there is no odd parent. The even edge above is the **unique** parent of every (y_j) with (j\le a-11).

## Terminal gap

At (j=a-10), the closed form for (G) gives
[
\frac{D_{a-10}}p
=\frac{103}{108}
 +\frac{74K-23}{27648q}
 -\frac{K-2}{2^a q}.
]
Using (q>K) and (a\ge38), both correction terms are positive and less than (1/100). Since
[
103/108-1/100>15/16,
\qquad
103/108+1/100<1,
]
we obtain
[
15p/16<D_{a-10}<p,
\qquad
p<y_{a-10}<17p/16.
]
This terminal state lies in an even-parent gap: it is above the upper endpoint (p-3) of the (k=K-3) band and below the lower endpoint (3p/2-1) of the (k=K-2) band.

Its only possible odd exponent is (t=0), since (X_{a-10}\equiv6\pmod9). But
[
(2y_{a-10}+5)/3\in(2p/3,3p/4),
]
which is the gap between the (k=K-4) and (k=K-3) odd source bands. Thus (y_{a-10}) has **no parent at all**.

Combining the uniqueness statements, the entire inverse-parent tree of (E) is
[
E\leftarrow h\leftarrow y_0\leftarrow y_1
\leftarrow\cdots\leftarrow y_{a-10},
]
and the final state is not the root (2). Therefore no `ResetChain` from (2) reaches (E).

## Exact modular certificate

For (a=38+54n), (2^{a-7}\pmod{243}) has period (162), so (a\pmod{162}) cycles through (38,92,146). Also (2^{54}\equiv82\pmod{162}), (2^{31}\equiv146\pmod{162}), and (146\cdot82\equiv146\pmod{162}). Hence (2^{a-7}\equiv146\pmod{162}) and (K\equiv116\pmod{162}) throughout this entire class.

The three residue rows are:

| (a\bmod162) | (K\bmod243) | (r\bmod162) | (2^K\bmod243) | (q\bmod243) | (2^r\bmod243) | (B\bmod243) |
|---:|---:|---:|---:|---:|---:|---:|
| 38 | 35 | 82 | 175 | 91 | 241 | 89 |
| 92 | 197 | 28 | 175 | 10 | 160 | 8 |
| 146 | 116 | 136 | 175 | 172 | 79 | 170 |

In all three rows, direct substitution gives the same decisive residues:
[
80p+2K+13-2B\equiv54\pmod{81},
]
so (X\equiv18\pmod{27}), and
[
248p-8B-10K+25\equiv81\pmod{243},
]
so (X_1\equiv9\pmod{27}). Also
[
A=4p+2K+1\equiv6\pmod9,
]
and
[
26368q+74K-23\equiv0\pmod{243},
]
so (G\equiv0\pmod9).

The small modular certificate is reproduced by `rho20_class2_mod162.mjs`. The period argument and three-row residue table, not a finite sample, establish the congruences for every (n\ge0).


## Shifted dyadic terminal-window family

The preceding family uses the single offset \(m=0\), hence \(g=103\). The same source-exact parent argument applies to a much larger set of \(K\)-values for each fixed \(a\).

Let
\[
a\ge38,\quad a\equiv38\pmod{54},\qquad
m\ge0,
\]
and put
\[
K=97\cdot2^{a-7}+48+486m,\qquad
g=103+972m,\qquad
p=2^K,\quad q=2^{K-a},\quad r=K+4-a.
\]
Then
\[
2K+7=97\cdot2^{a-6}+g,\qquad
x=\frac{2K+7}{2^a}=\frac{97}{64}+\frac{g}{2^a}.
\]
Use the same \(B,D,E\) definitions as above. For an integer \(s\) with
\[
19\le s\le a-3,\qquad
\frac{15}{16}<\theta_s:=\frac{256g}{27\cdot2^s}<\frac{31}{32}, \tag{10}
\]
the complete inverse-parent graph of \(E\) is again a single chain ending at a non-root leaf:
\[
E\leftarrow h_0\leftarrow y_0\leftarrow y_1
\leftarrow\cdots\leftarrow y_{a-s}.
\]
There are exactly \(a-s\) same-level even-parent edges. In particular,
\[
\neg\,\operatorname{ResetChain}(2,E).
\]

### The modular phase survives every shift

The three-row table in the preceding section is indexed by \(a\bmod162\in\{38,92,146\}\). Replacing the baseline \(K_0=97\cdot2^{a-7}+48\) by \(K=K_0+486m\) preserves:
- \(K\bmod243\) and \(K\bmod162\);
- \(2^K\bmod243\), \(2^{K-a}\bmod243\), and \(2^{K+4-a}\bmod243\), since \(486\) is a multiple of \(162\);
- \((2K+7)\bmod243\), since \(972\) is a multiple of \(243\).

Thus the table's decisive residues are unchanged for every \(m\ge0\). With
\[
X=2E+5,\quad X_1=2h_0+5,\quad
A=4p+2K+1,\quad L=K-2,
\]
and
\[
G=\frac{256gq+74K-23}{27},
\]
we have, uniformly in \(a,m\),
\[
X\equiv18\pmod{27},\qquad
X_1\equiv9\pmod{27},\qquad
A\equiv6\pmod9,\qquad
G\equiv0\pmod9. \tag{11}
\]
In particular \(v_3(X)=v_3(X_1)=2\).

### The two initial odd parents remain unique

Condition (10), together with \(a-s\ge3\), gives
\[
0<\frac{g}{2^a}
<\frac{837}{65536}<\frac3{64},
\qquad
\frac{97}{64}<x<\frac{25}{16}.
\]
Also \(K<2^a\) and \(K\ge2a\), so \(q=2^{K-a}\ge2^a>K\).

The exact identities are
\[
\frac Xp=\frac{21}{2}-\frac{32g}{3\cdot2^a}
+\frac{2K+13}{3p},
\qquad
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p},
\]
\[
\frac{X_1}{p}
=6-\frac{128g}{9\cdot2^a}-\frac{10K-25}{9p}.
\]
Since \(x<25/16\), \(X/p>10\). Since \(q>K\) and \(g\ge103\), the final positive term in \(X/p\) is smaller than \(32g/(3\cdot2^a)\), so \(X/p<21/2\). Consequently
\[
\frac{10}{3}<\frac{X}{3p}<\frac72,
\qquad
\frac{20}{9}<\frac{2X}{9p}<\frac73.
\]
The first coordinate is in the odd-source band at level \(K-1\), while the second is in the gap \((2p,3p)\). Thus \(E\) has exactly the \(t=0\) parent
\[
h_0=\frac{2X}{3}-4p-K-4.
\]
Moreover \(5<E/p<6\), so \(E\) has no even parent. The bounds \(10<X/p<21/2\) also give \(2p<h_0<3p\), excluding every even parent of \(h_0\).

From \(g/2^a<837/65536\) and \(q>K\),
\[
\frac{X_1}{p}
>6-\frac{93}{512}-\frac1{1000}
>\frac{29}{5},
\qquad
\frac{X_1}{p}<6.
\]
Therefore \(X_1/3\in(29p/15,2p)\) lies in the odd-source band at level \(K-2\), whereas \(2X_1/9\in(58p/45,4p/3)\) lies in the gap \((p,3p/2)\). Hence \(h_0\) has exactly the \(t=0\) parent
\[
y_0=\frac{2X_1}{3}-2p-K-3.
\]
The same bounds put \(y_0\) in the level-\(L\) even-child band. Direct substitution gives
\[
D_0:=2p-y_0=\frac{256gq+47K+31}{27},
\qquad
G:=D_0+L=\frac{256gq+74K-23}{27}. \tag{12}
\]

### The even spine terminates inside a strict parent gap

Define
\[
D_j=2^jG-L,\qquad y_j=2p-D_j.
\]
Then \(D_{j+1}=2D_j+L\), and the even parent of \(y_j\), whenever admissible, is exactly \(y_{j+1}\) at level \(L\). For every \(j\le a-s\),
\[
\frac{D_j}{p}
=\frac{256g}{27\cdot2^{a-j}}+\varepsilon_j,\qquad
\varepsilon_j=
\frac{2^j(74K-23)}{27p}-\frac{K-2}{p}.
\]
Using \(j\le a-s\), \(q>K\), \(s\ge19\), and \(a\ge38\),
\[
|\varepsilon_j|
<
\frac{74}{27\cdot2^{19}}+\frac1{2^{38}}
<\frac1{1000}. \tag{13}
\]
At the terminal index \(j_*=a-s\), (10) and (13) imply
\[
\frac9{10}<\frac{D_{j_*}}p<\frac{49}{50}.
\]
At the preceding index,
\[
\frac{D_{j_*-1}}p
<
\frac{31}{64}+\frac1{1000}<\frac12.
\]
Since \(D_j\) is increasing and \(D_0>3\), every \(0\le j<j_*\) satisfies
\[
3< D_j<\frac p2,\qquad
\frac{3p}{2}<y_j\le2p-3.
\]
Thus each such \(y_j\) has exactly the displayed even parent at level \(L\), with no other even level possible.

For every spine state,
\[
X_j:=2y_j+5=A-2^{j+1}G\equiv6\pmod9
\]
by (11). Hence only the odd exponent \(t=0\) is possible. Its source coordinate lies in
\[
\frac{2y_j+5}{3}\in(p,4p/3),
\]
strictly between the adjacent odd-source bands at levels \(K-2\) and \(K-1\). There is no odd parent on the spine before the terminal state.

At \(j_*\), the terminal bound gives
\[
p<y_{j_*}<\frac{11p}{10}.
\]
It is outside the adjacent even-child bands, whose gap here is \((p-3,3p/2-1)\). Its only possible odd source coordinate is
\[
\frac{2y_{j_*}+5}{3}\in(2p/3,3p/4),
\]
where the upper bound follows from \(p>100\). This is the strict gap between the odd-source bands at levels \(K-4\) and \(K-3\). So \(y_{j_*}\) has no parent at all.

The exact source grammar in FirstInverseComplete.lean has only the two parent arms used above, and ResetChain.lean proves the equivalence between ResetChain and genuine blank-root reset reachability. The unique chain therefore cannot reach the root \(2\).

### How many targets are covered?

Condition (10) is equivalent to
\[
810\cdot2^s<8192(103+972m)<837\cdot2^s. \tag{14}
\]
For each \(s\ge19\), the corresponding open interval for \(g\) has width
\[
\frac{27\cdot2^s}{8192}\ge1728>972.
\]
It therefore contains at least one integer \(g\equiv103\pmod{972}\), and its lower endpoint is already greater than \(103\), so \(m\ge0\). The intervals for successive \(s\) are disjoint. Consequently, for every \(a\equiv38\pmod{54}\), \(a\ge38\), there are at least \(a-21\) distinct shifted \(K\)-values covered by this theorem (one for each \(19\le s\le a-3\)); each has a complete parent chain ending at a leaf. The number of choices grows exponentially with \(a\).

For \(a=38\), exact integer interval counting gives \(233{,}015\) distinct \(m\)-values across \(s=19,\ldots,35\). The counts at the two ends are \(2\) for \(s=19\) and \(116{,}508\) for \(s=35\). The exact floor-count and modular-residue reproducer is rho20_class2_dyadic_terminal_windows.mjs.

This is a paper-level extension of the \(m=0\) theorem, not a Lean-compiled theorem and not a decision of all rho-20 candidates. It is an additional large set of excluded fatal targets inside the residual \(a\equiv2\pmod{18}\) class.

## Scope and next steps

The baseline theorem resolves one explicit (K)-ray in the (a\bmod54=38) phase. The shifted terminal-window theorem above excludes at least (a-21) additional (K)-values for each (a\equiv38\pmod{54}), with (N(38)=233{,}015) exact shifted values. The (a\bmod54=2) and (20) phases remain open. The next useful work is:

1. Formalize the modular certificate and the (q>K) inequalities in Lean.
2. Prove the unique-parent lemmas directly for `CascadeResetInverse.ResetParent`.
3. Deduce `¬ ResetChain 2 E` and compile it through the existing manual source workflow.
4. Ask Agent 10 to check the (D_j), (G), and terminal-gap algebra independently before promoting any synthesis claim.

The underlying grammar is source-complete in `FirstInverseComplete.lean` and `ResetChain.lean`; this note supplies a new parameterized parent-tree argument, not a claim that the whole #746 machine is nonhalting.
