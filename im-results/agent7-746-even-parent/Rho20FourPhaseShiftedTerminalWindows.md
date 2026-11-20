# Shifted rho-20 terminal-window exclusions across four modulo-54 phases

**Status.** This is a new paper-level arithmetic extension over the source-certified first-reset inverse grammar. It has not yet been Lean-compiled. It extends the single-K-ray results in the 14/32/46 phase note (results/2026-11-19-machine-746-rho20-14-32-46-phase-root-exclusion.md) and the phase-38 class-2 note (Rho20Class2-38mod162.md) to large families of shifted K-values. Keep it in im-results pending adversarial review and formalization.

## Theorem

Let \(a\ge32\) be even and satisfy
\[
a\bmod54\in\{14,32,38,46\}.
\]
Choose \(m\ge0\), and put
\[
K=97\cdot2^{a-7}+48+486m,\qquad
g=103+972m,\qquad
p=2^K,\quad q=2^{K-a},\quad r=K+4-a,
\]
\[
B=(2K+7)2^r,\qquad
D=\frac{B-16p+2K+1}{3},\qquad
E=8p+K-D.
\]
Then \(K\equiv2\pmod6\) and \(K+6a\equiv20\pmod{54}\), so \(E\) is the same \((t=0,q=0)\) rho-20 fatal-source candidate.

Suppose there is an integer \(s\) such that
\[
19\le s\le a-3,\qquad
\frac{15}{16}<\theta_s:=\frac{256g}{27\cdot2^s}<\frac{31}{32}. \tag{1}
\]
Set \(L=K-2\). The complete inverse-parent graph of \(E\) is:
- if \(a\equiv38\pmod{54}\), one chain
\[
E\leftarrow h_0\leftarrow y_0\leftarrow y_1
\leftarrow\cdots\leftarrow y_{a-s};
\]
- if \(a\equiv14,32,\) or \(46\pmod{54}\), the same chain together with one additional first-parent leaf \(h_2\):
\[
E\leftarrow h_2,\qquad
E\leftarrow h_0\leftarrow y_0\leftarrow y_1
\leftarrow\cdots\leftarrow y_{a-s}.
\]
There are exactly \(a-s\) same-level even-parent edges on the \(h_0\)-branch, and every terminal node is a leaf strictly greater than \(2\). Hence
\[
\neg\,\operatorname{ResetChain}(2,E).
\]

## 1. Shift-invariant modular data

Write \(K_0=97\cdot2^{a-7}+48\). The existing exact modular tables cover the three lifts \(a\bmod162\) in each of the four phases:
- phases 14, 32, and 46: the nine rows in results/2026-11-19-machine-746-rho20-14-32-46-phase-root-exclusion.md;
- phase 38: the three rows in Rho20Class2-38mod162.md.

The shift \(K=K_0+486m\) preserves \(K\bmod243\) and \(K\bmod162\). It also preserves \(2^K\), \(2^{K-a}\), and \(2^{K+4-a}\pmod{243}\), because \(486\) is a multiple of \(162\), and preserves \(2K+7\bmod243\), because \(972\) is a multiple of \(243\). Since
\[
2K+7=97\cdot2^{a-6}+g,
\]
the changed coefficient \(g\) is also unchanged modulo \(243\). Thus all decisive residues in the existing tables persist for every \(m\ge0\).

The resulting phase summary is:

| \(a\bmod54\) | \(K\bmod54\) | \(X\bmod81\) | \(X_1\bmod27\) | \(A\bmod9\) | \(G\bmod9\) | \(X_2\bmod3\) |
|---:|---:|---:|---:|---:|---:|---:|
| 14 | 44 | 54 | 12 | 6 | 7 | 2 |
| 32 | 44 | 27 | 3 | 6 | 4 | 1 |
| 38 | 8 | 18 | 9 | 6 | 0 | — |
| 46 | 14 | 27 | 18 | 0 | 6 | 1 |

Here
\[
X=2E+5,\quad h_0=\frac{2X}{3}-4p-K-4,\quad X_1=2h_0+5,
\]
\[
A=4p+2K+1,\quad
G=\frac{256gq+74K-23}{27},
\]
and, in phases 14, 32, and 46 only,
\[
h_2=\frac{8X}{27}-2p-K-3,\qquad
X_2=2h_2+5=\frac{16X}{27}-4p-2K-1.
\]
In phases 14, 32, and 46, \(v_3(X)=3\); in phase 38, \(v_3(X)=2\). Also \(v_3(X_1)=1\) in phases 14 and 32, and \(v_3(X_1)=2\) in phases 38 and 46. The table shows \(3\nmid X_2\) whenever \(h_2\) exists.

For phases 14 and 32, \(A\equiv0\pmod3\) and \(G\equiv1\pmod3\). For phase 38, \(A\equiv6\pmod9\) and \(G\equiv0\pmod9\). For phase 46, \(A\equiv0\pmod9\) and \(G\equiv6\pmod9\). These are the only spine-residue cases needed below.

## 2. Uniform scale bounds and the initial parents

Condition (1) and \(a-s\ge3\) imply
\[
0<\frac{g}{2^a}
=\frac{27\theta_s}{256}\,2^{s-a}
<\frac{837}{65536}<\frac3{64},
\qquad
\frac{97}{64}<x:=\frac{2K+7}{2^a}<\frac{25}{16}.
\]
Moreover
\[
K=\frac{97\cdot2^{a-6}+g-7}{2}<2^a,
\qquad K\ge2a,
\]
so \(q=2^{K-a}\ge2^a>K\).

The exact identities
\[
\frac Xp=\frac{21}{2}-\frac{32g}{3\cdot2^a}
+\frac{2K+13}{3p},
\qquad
\frac Ep=\frac{40-16x}{3}+\frac{K-1}{3p},
\]
give
\[
10.3<\frac Xp<10.5,\qquad 5<\frac Ep<5.251<6.
\]
For the upper bound on \(X/p\), use \(2K+13<32gq\); for the lower bound, use \(x<25/16\). Thus \(E\) lies strictly between the adjacent even-parent bands at levels \(K-1\) and \(K\).

The odd-source coordinates at \(E\) satisfy
\[
3.43<\frac{X}{3p}<3.5,\qquad
2.28<\frac{2X}{9p}<\frac73,\qquad
1.52<\frac{4X}{27p}<\frac{14}{9}.
\]
The first is in the odd-source band at level \(K-1\), the second is in the gap \((2p,3p)\), and the third is in the band at level \(K-2\). In phases 14, 32, and 46, \(v_3(X)=3\), so the only possible odd exponents are \(t=0,1,2\), giving exactly two parents:
\[
h_0=\frac{2X}{3}-4p-K-4,\qquad
h_2=\frac{8X}{27}-2p-K-3.
\]
In phase 38, \(v_3(X)=2\), so only \(t=0,1\) are possible and \(E\) has only the parent \(h_0\).

The bound on \(X/p\) gives \(2p<h_0<3p\), so \(h_0\) has no even parent. Also
\[
\frac{X_1}{p}
=6-\frac{128g}{9\cdot2^a}-\frac{10K-25}{9p}
>6-\frac{93}{512}-\frac1{1000}
>\frac{29}{5},
\qquad
\frac{X_1}{p}<6.
\]
Thus
\[
\frac{X_1}{3p}\in(29/15,2),\qquad
\frac{2X_1}{9p}\in(58/45,4/3).
\]
The first coordinate lies in the odd-source band at level \(K-2\), while the second lies in the gap \((p,3p/2)\). In phases 14 and 32, \(v_3(X_1)=1\), so only \(t=0\) is possible. In phases 38 and 46, \(v_3(X_1)=2\), and the \(t=1\) coordinate is still in that gap. Hence \(h_0\) has exactly one parent,
\[
y_0=\frac{2X_1}{3}-2p-K-3.
\]

When \(h_2\) exists, its height satisfies
\[
\frac{21}{20}<\frac{h_2}{p}<\frac{10}{9}<\frac32.
\]
It is therefore in an even-parent gap. The table gives \(X_2\not\equiv0\pmod3\), so \(h_2\) has no odd parent either. It is a leaf.

## 3. The \(h_0\)-branch and its terminal window

Let \(D_0=2p-y_0\). Direct substitution gives
\[
D_0=\frac{256gq+47K+31}{27},\qquad
G=D_0+L=\frac{256gq+74K-23}{27}. \tag{2}
\]
Define
\[
D_j=2^jG-L,\qquad y_j=2p-D_j.
\]
Then
\[
D_{j+1}=2D_j+L,\qquad y_{j+1}=2y_j-2p-L,
\]
and for \(j\le a-s\),
\[
\frac{D_j}{p}
=\frac{256g}{27\cdot2^{a-j}}+\varepsilon_j,\qquad
\varepsilon_j=
\frac{2^j(74K-23)}{27p}-\frac{K-2}{p}.
\]
Using \(q>K\), \(s\ge19\), and \(a\ge32\),
\[
|\varepsilon_j|
<
\frac{74}{27\cdot2^{19}}+\frac1{2^{32}}
<\frac1{1000}. \tag{3}
\]

At \(j_*=a-s\), (1) and (3) imply
\[
\frac9{10}<\frac{D_{j_*}}p<\frac{49}{50},
\qquad
p<y_{j_*}<\frac{11p}{10}.
\]
At the preceding index,
\[
\frac{D_{j_*-1}}p
<
\frac{31}{64}+\frac1{1000}<\frac12.
\]
Since \(D_j\) is increasing and \(D_0>3\), every \(j<j_*\) satisfies
\[
3<D_j<\frac p2,\qquad
\frac{3p}{2}<y_j\le2p-3.
\]
Thus every \(y_j\) before the terminal state has exactly one even parent, at level \(L\), namely \(y_{j+1}\).

It remains to exclude odd parents. For every spine state,
\[
X_j:=2y_j+5=A-2^{j+1}G.
\]
In phases 14 and 32, \(A\equiv0\pmod3\) and \(G\equiv1\pmod3\), so \(X_j\not\equiv0\pmod3\). In phase 38, \(X_j\equiv6\pmod9\). In phase 46, \(X_j\equiv-6\cdot2^{j+1}\pmod9\), which is always \(3\) or \(6\pmod9\). Therefore phases 14 and 32 have no odd parent at any spine node; phases 38 and 46 have \(v_3(X_j)=1\), so only \(t=0\) needs checking.

For \(j<j_*\),
\[
\frac{2y_j+5}{3}\in(p,4p/3),
\]
the gap between the odd-source bands at levels \(K-2\) and \(K-1\). At the terminal state,
\[
p<y_{j_*}<11p/10
\quad\Longrightarrow\quad
\frac{2y_{j_*}+5}{3}\in(2p/3,3p/4),
\]
using \(p>100\). This is the gap between the odd-source bands at levels \(K-4\) and \(K-3\). Thus the terminal state has no parent at all.

The exact source grammar in FirstInverseComplete.lean has only the even and odd parent arms exhausted above. ResetChain.lean proves equivalence between reset-parent ancestry and genuine blank-root reset reachability. The \(h_0\)-branch therefore cannot reach \(2\), and the optional \(h_2\)-branch is already a leaf.

## 4. Number of excluded targets

Condition (1) is equivalent to
\[
810\cdot2^s<8192(103+972m)<837\cdot2^s. \tag{4}
\]
For each \(s\ge19\), the interval for \(g\) has width
\[
\frac{27\cdot2^s}{8192}\ge1728>972.
\]
It therefore contains at least one integer \(g\equiv103\pmod{972}\), and the lower endpoint exceeds \(103\), so \(m\ge0\). The intervals for successive \(s\) are disjoint. Hence for every admissible \(a\) there are at least \(a-21\) distinct shifted \(K\)-values excluded by the theorem.

Define the exact count
\[
N(a)=\sum_{s=19}^{a-3}
\#\left\{m\in\mathbb N:
810\cdot2^s<8192(103+972m)<837\cdot2^s
\right\}.
\]
Then
\[
N(32)=3{,}639,\quad
N(38)=233{,}015,\quad
N(46)=59{,}652{,}322,\quad
N(68)=250{,}199{,}979{,}298{,}359.
\]
The count grows exponentially:
\[
N(a)=\frac{27}{31{,}850{,}496}\,2^a+O(a).
\]
The exact floor-count and 12-row modular reproducer is rho20_four_phase_shifted_terminal_windows.mjs.

This result covers additional shifted fatal targets in four of the modulo-54 phases, not all candidate K-values in those phases. The residual phases \(a\bmod54=2,20\), phase 50 outside already excluded cylinders, other fatal-source families, other #746 halting gates, and BB(6) remain open. This is intermediate paper-level research, not a Lean-certified result.
