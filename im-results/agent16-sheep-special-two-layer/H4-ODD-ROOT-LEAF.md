# h=4 odd exceptional-state root-leaf family

**Status.** This closes a positive-density subfamily of the previously open \(h=4\), \(a\equiv67\pmod{162}\) sector for exceptional targets \(Y_a=3\cdot2^a\). It is an all-time blank-even-root exclusion for the explicit exponents below, not a halting-power exclusion and not a BB(6) decision. The inverse arithmetic is exact; the new two-layer composition is not yet a single Lean theorem importing the original source.

## Theorem

Let \(R\) be the following disjoint union of residue classes, with \(r\ge0\):

- \(s=0\): \(r\equiv1,7,13,19\pmod{30}\), or \(r\equiv9,15\pmod{18}\).
- \(s=1\): \(r\equiv11\pmod{18}\), or \(r\equiv23,41\pmod{54}\).
- \(s=2\): \(r\equiv17\pmod{54}\), or \(r\equiv35,143\pmod{162}\).
- \(s=3\): \(r\pmod{4860}\) belongs to
  \[
  \{53,377,593,917,1025,1241,1349,1565,1997,2213,2321,2537,
  2861,2969,3185,3293,3833,3941,4157,4265,4481,4805\}.
  \]
- \(s=4\): \(r\equiv485\pmod{486}\), or \(r\equiv161,647\pmod{1458}\).
- \(s=5\): \(r\equiv809\pmod{1458}\), or \(r\equiv1781,3239\pmod{4374}\).

For every \(r\in R\), put
\[
a=1201+1458r,\quad
Y_a=3\cdot2^a,\quad
X_a=\frac{4(2^{a+1}-1)}3,\quad
x_a=\frac{2^{a+10}-1868}{2187}.
\]
Then the only even predecessor of \(Y_a\) is \(X_a\), the only even predecessor of \(X_a\) is \(x_a\), and \(x_a\) has no even predecessor. Consequently \(Y_a\) is not reachable from the blank even root \(10\).

The \(r\)-set has density \(1649/4374\). Since \(a\) advances by \(1458\), this adds exponent density
\[
\frac{1649}{4374\cdot1458}=\frac{1649}{6377292}.
\]
The set is disjoint from the previously certified \(158/243\) exceptional-target union (the six \(A_0,A_1,A_2,A_3,A_3',A_5\) progressions and the \(a\equiv2\pmod4\) family). The combined stated exceptional-target exclusion is therefore
\[
\frac{158}{243}+\frac{1649}{6377292}
=\frac{4148201}{6377292}
\approx65.0464\%.
\]

## 1. The unique \(h=4\) parent of \(X_a\)

Write \(a=67+162k\). The already established uniform generic-source cutoff says that a generic even predecessor \(2^b v\) of \(X_a\), with hidden length \(h\ge1\), must have \(b\le2h+4\); for \(h=4\), it is enough to test \(1\le b\le12\). The exact \(h=4\) source equation is
\[
243(2^{b+1}+1)v+243(2b-3)=32(2^{a+3}-7).
\]
Thus, with \(Q_b=2^{b+1}+1\) and \(M_b=243Q_b\), a necessary condition is
\[
32(2^{70+162k}-7)\equiv243(2b-3)\pmod{M_b}.
\]
The exact period \(P_b\) of \(2^{162}\pmod{M_b}\), with the additional \(k\not\equiv2\pmod3\) filter for exact valuation \(h=4\), gives this exhaustive table:

| \(b\) | \(P_b\) | admissible \(k\)-residues satisfying the congruence |
|---:|---:|---|
| 1 | 2 | none |
| 2 | 9 | \(k\equiv7\pmod9\) |
| 3 | 4 | none |
| 4 | 15 | none |
| 5 | 2 | none |
| 6 | 21 | none |
| 7 | 8 | none |
| 8 | 27 | none |
| 9 | 10 | none |
| 10 | 33 | none |
| 11 | 4 | none |
| 12 | 39 | none |

The combined period for the table is \(\operatorname{lcm}(P_b,3)\), so the valuation filter is included even when \(3\nmid P_b\). Hence the only generic branch is \(b=2,\ k\equiv7\pmod9\), giving exactly \(a=1201+1458r\) and
\[
v_a=\frac{2^{a+8}-467}{2187},\qquad x_a=4v_a.
\]
The congruence makes \(v_a\) an integer; its numerator is odd and it is at least five.

All lower hidden-length branches are absent in this progression:
\[
\begin{array}{c|c|c}
(h,b)&\text{required exponent residue}&\text{actual residue}\\ \hline
(0,2)&a\equiv11\pmod{18}&a\equiv13\pmod{18}\\
(0,4)&a\equiv3\pmod{30}&a\equiv1+18r\pmod{30}\ne3\\
(1,1)&a\equiv1\pmod{12}&a\equiv7\pmod{12}\\
(1,2)&a\equiv37\pmod{54}&a\equiv13\pmod{54}\\
(1,3)&a\equiv13\pmod{24}&a\equiv7\text{ or }19\pmod{24}\\
(2,2)&a\equiv103\pmod{162}&a\equiv67\pmod{162}\\
(3,1)&a\equiv13\pmod{108}&a\equiv67\pmod{108}\\
(3,2)&a\equiv445\pmod{486}&a\equiv229\pmod{486}.
\end{array}
\]
Also \(v_3(2^{1204}-7)=5\) and \(v_3(2^{1458}-1)=7\), so \(v_3(X_a-1)=4\) for every \(r\ge0\).

The exceptional source \(3\cdot2^d\) is impossible as a parent of \(X_a\). Its equation would be
\[
2^{a+7}=g(d):=729\cdot2^d+243d+598.
\]
The function \(g\) is strictly increasing, and for \(a\ge1201\)
\[
2^{a+7}-g(a-3)=295\cdot2^{a-3}-243a+131>0,
\]
\[
g(a-2)-2^{a+7}=434\cdot2^{a-3}+243a+112>0.
\]
Thus \(g(a-3)<2^{a+7}<g(a-2)\), which no integer \(d\) can satisfy.

Finally, \(a\) is odd and \(a\equiv3\) or \(7\pmod8\). The established direct-parent grammar for \(Y_a\) therefore gives \(X_a\) as its unique even predecessor. This proves the chain \(Y_a\leftarrow X_a\leftarrow x_a\).

## 2. The terminal parent \(x_a\) has no predecessor

We have
\[
x_a-1=\frac{2^{1211+1458r}-4055}{3^7}.
\]
For \(r\in R\), let \(s=v_3(x_a-1)\). Exact enumeration modulo \(3^{s+8}\), whose \(r\)-period is \(3^{s+1}\), gives the complete exact-valuation root classes through \(s=5\):
\[
\begin{array}{c|c|c}
s&\text{exact }r\text{ residues modulo }3^{s+1}&\text{odd lifts used in }R\\ \hline
0&0,1\pmod3&r\equiv1,3\pmod6\\
1&2,5\pmod9&r\equiv11\pmod{18};\ 5,23,41\pmod{54}\\
2&8,17\pmod{27}&35,17\pmod{54}\\
3&26,53\pmod{81}&r\text{ odd in these classes}\\
4&161,242\pmod{243}&161,485\pmod{486}\\
5&80,323\pmod{729}&809,323\pmod{1458}.
\end{array}
\]
The family \(R\) selects only root classes and odd lifts with no generic parent.

Suppose a generic even source \(2^c v\), \(c\ge1\), \(v\ge5\) odd, were a predecessor of \(x_a=1+3^s w\). The source law gives
\[
2^{s+1}(x_a-1)=3^s\big((2^{c+1}+1)v+2c-3\big),
\]
hence, with \(Q_c=2^{c+1}+1\),
\[
2^{a+s+11}=3^{s+7}Q_c v+K_{s,c},\qquad
K_{s,c}=2^{s+1}\cdot4055+3^{s+7}(2c-3).
\tag{1}
\]

A uniform signed-power gap cuts this search off at \(c\le2s+16\). Indeed, at \(c=2s+17\),
\[
K_{s,c}=2^{s+1}\cdot4055+3^{s+7}(4s+31)<2^{2s+17}.
\]
The inequality holds at \(s=0\), and the left side grows by at most a factor four when \(s\) increases by one. Also \(K_{s,c+1}-K_{s,c}=2\cdot3^{s+7}<2^{2s+17}\le2^c\) for \(c\ge2s+17\). Thus \(1<K_{s,c}<2^c\) for all \(c\ge2s+17\). Modulo \(Q_c\), (1) would make this odd integer a power-of-two residue. But since \(2^{c+1}\equiv-1\pmod{Q_c}\), every such residue is \(2^j\) or \(Q_c-2^j\), \(0\le j\le c\); none lies in \((1,2^c)\). Therefore \(c\le2s+16\).

For each remaining \(c\), put \(t=v_3(Q_c)\),
\[
P(s,c)=\operatorname{lcm}\!\left(3^{s+t},
\frac{2(c+1)}{\gcd(2(c+1),1458)}\right),\qquad
R(s,c)=\operatorname{lcm}(2\cdot3^{s+1},P(s,c)).
\]
This is a period for the congruence (1) and for the parity/3-adic root filter: the 3-primary order of \(2^{1458}\) modulo \(3^{s+7+t}\) is \(3^{s+t}\), while \(2^{2(c+1)}\equiv1\pmod{Q_c/3^t}\). Exhausting \(r\pmod{R(s,c)}\) gives every possible generic-parent congruence:

| \(s\) | tested \(c\) | all possible congruence hits |
|---:|---:|---|
| 0 | 1–16 | \(c=2,\ r\equiv3\pmod{18}\); \(c=4,\ r\equiv25\pmod{30}\) |
| 1 | 1–18 | \(c=2,\ r\equiv5\pmod{54}\) |
| 2 | 1–20 | \(c=2,\ r\equiv89\pmod{162}\) |
| 3 | 1–22 | \(c=2,\ r\equiv215\pmod{486}\); \(c=3,\ r\equiv107,215\pmod{324}\); \(c=4,\ r\equiv269\pmod{810}\) |
| 4 | 1–24 | \(c=2,\ r\equiv1133\pmod{1458}\) |
| 5 | 1–26 | \(c=2,\ r\equiv323\pmod{4374}\) |

The displayed definition of \(R\) excludes every listed hit. For \(s=3\), the 22 residues modulo 4860 are exactly the odd lifts in the two exact root classes that avoid the \(c=2,3,4\) hits. Thus no generic even source can precede \(x_a\).

It remains to exclude the exceptional source \(3\cdot2^c\). If it were a predecessor, its odd successor would have to be
\[
T_s=1+2^s w=3\cdot2^c+c+3.
\]
For \(s=0\), \(T_0=x_a\), and
\[
\frac{x_a}{2^a}=\frac{1024}{2187}-\frac{1868}{2187\cdot2^a}
\in\left(\frac38,\frac12\right).
\]
Any candidate has \(c\ge4\), so \(3\cdot2^c+c+3\) lies strictly between \(3\cdot2^c\) and \(4\cdot2^c\). The interval therefore forces \(c=a-3\). But
\[
x_a-(3\cdot2^{a-3}+a)
=\frac{295\cdot2^{a-3}-2187a-1868}{2187}>0.
\]
The numerator is positive at \(a=2659\) and has positive forward difference \(295\cdot2^{a-3}-2187\) for \(a\ge10\), so equality is impossible.

For \(1\le s\le5\),
\[
\frac{T_s}{2^a}
=C_s+\frac{3^{s+7}-2^s\cdot4055}{3^{s+7}2^a},
\qquad C_s=\frac{2^{s+10}}{3^{s+7}}.
\]
All \(a\) in the family satisfy \(a\ge2659\); the correction has absolute value below \(10^{-4}\), so the exact ratio remains in the following interval (the interval margins exceed \(10^{-4}\)):

| \(s\) | \(C_s\) | interval containing \(T_s/2^a\) | consequence |
|---:|---:|---:|---|
| 1 | \(2048/6561\) | \((1/4,3/8)\) | a gap between the possible source intervals; impossible |
| 2 | \(4096/19683\) | \((3/16,1/4)\) | only \(c=a-4\) could fit |
| 3 | \(8192/59049\) | \((1/8,3/16)\) | a gap; impossible |
| 4 | \(16384/177147\) | \((1/16,3/32)\) | a gap; impossible |
| 5 | \(32768/531441\) | \((3/64,1/16)\) | only \(c=a-6\) could fit |

In the two non-gap cases, the equality \(2^s w=3\cdot2^c+c+2\), with \(c\ge s\), forces \(2^s\mid c+2\). For \(s=2\) or \(5\), this makes \(c\) even. But \(a\) is odd and the only candidates \(a-4,a-6\) are odd. Contradiction. This excludes every exceptional predecessor as well.

Therefore \(x_a\) has no even predecessor. Since \(x_a>10\), it cannot occur on a blank-root trajectory, and neither can \(X_a\) or \(Y_a\).

## 3. Density, disjointness, and remaining frontier

The selected classes have density
\[
\frac2{15}+\frac19+\frac5{54}+\frac5{162}
+\frac{22}{4860}+\frac5{1458}+\frac5{4374}
=\frac{1649}{4374}
\]
in \(r\), hence \(1649/6377292\) among all \(a\). The arithmetic verifier checks pairwise disjointness and CRT-disjointness from the prior six progressions and the \(a\equiv2\pmod4\) family.

This is only a subfamily of the \(h=4\), \(a\equiv67\pmod{162}\) sector: other \(k\)-residues, other \(r\)-classes, and hidden lengths \(s\ge6\) remain open. The proof also does not turn these intermediate-state exclusions into a halting-power exclusion. The next decisive step remains a source-importing Lean composition and, ultimately, a connection to every possible halting power.

## Reproduction

Run **python3 im-results/agent16-sheep-special-two-layer/verify_h4_root_leaf.py** from the repository root. It checks the finite modular periods, all listed root classes and parent hits, the special-source interval inequalities, the density, and disjointness. The arithmetic audit is exact Python-integer computation; the new two-layer theorem is not yet Lean-kernel compiled.
