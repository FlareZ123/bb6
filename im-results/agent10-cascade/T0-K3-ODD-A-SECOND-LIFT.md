# Odd-a K ≡ 3 (mod 6): second-lift exclusions for the two residual t=0 phases

**Status:** paper-level continuation of [the seven-of-nine phase theorem](T0-K3-ODD-A-SEVEN-OF-NINE.md). The modulo-81 tables were checked by the accompanying exact modular script. The parent-gap arguments are exact inequalities against the source ResetParent bands, but this continuation has not been Lean-formalized or independently reviewed. It remains in im-results.

## Theorem

Use the notation of the preceding theorem:
\[
p=2^K,\quad c=2K+7,\quad x=c/2^a,\quad
B=c2^{K+4-a},\quad
E=(40p+K-1-B)/3,\quad X=2E+5,
\]
with odd \(a\ge13\), \(K\equiv3\pmod6\), and \(x\in[97/64,13/8]\).

Define the narrower interval
\[
\mathcal W=
\left[\frac{803}{512},\frac{415}{256}-\frac1{1024}\right]
=\left[\frac{1606}{1024},\frac{1659}{1024}\right].
\tag{1}
\]
Its width is \(53/1024\). As an interval for \(K\), its width is
\[
\frac{53\cdot2^a}{2048}>54
\qquad(a\ge13),
\tag{2}
\]
so it contains an integer in every residue class modulo \(54\).

There are two further exact exclusions.

1. In the exceptional phase \(K\equiv12-3a\pmod{54}\), the entry \(E\) is parentless whenever
\[
a\bmod54\notin S_0,\qquad
S_0=\{3,5,7,15,27,35,37,47,49\}.
\tag{3}
\]
This conclusion holds throughout the full interval \(97/64\le x\le13/8\), not only in \(\mathcal W\).

2. In the exceptional phase \(K\equiv48-3a\pmod{54}\), the entry \(E\) is parentless whenever
\[
a\bmod54\notin S_3,\qquad
S_3=\{1,3,5,17,31,33,43,45,47\},
\tag{4}
\]
and \(x\in\mathcal W\).

Together with the previous seven-of-nine theorem, this implies that for every odd \(a\ge13\) with
\[
a\bmod54\notin S_0\cup S_3
=\{1,3,5,7,15,17,27,31,33,35,37,43,45,47,49\},
\tag{5}
\]
every t=0 entry \(E\) in the full nine-class family with \(x\in\mathcal W\) is outside the genuine blank-root ResetChain. The complement of the union in the odd residues modulo \(54\) is
\[
\{9,11,13,19,21,23,25,29,39,41,51,53\},
\]
a set of 12 of the 27 odd residue classes. This is a parameter-family statement, not a density of machines or halting histories.

## 1. The \(X\equiv0\pmod9\) phase: the \(v_3(X)=2\) lift is parentless

In this phase \(K\equiv12-3a\pmod{54}\). Since \(2\) has order \(54\) modulo \(81\), the expression
\[
X=\frac{80\cdot2^K+2K+13-2(2K+7)2^{K+4-a}}{3}
\]
modulo \(27\) is determined by \(a\bmod54\) and \(K\bmod54\).

The exact lift table partitions the odd residues \(a\bmod54\) as follows:
\[
\begin{array}{c|l}
X\bmod27 & a\bmod54\\ \hline
0 &
3,5,7,15,27,35,37,47,49\\
9 &
9,17,19,29,31,39,41,43,51\\
18 &
1,11,13,21,23,25,33,45,53.
\end{array}
\tag{6}
\]
Thus outside \(S_0\), \(v_3(X)=2\) exactly. The odd-parent equation for \(E\) forces \(t=1\), with odd parameter \(d=X/9\). Its actual source-band parameter is \(2d\), and
\[
\frac{2d}{p}
=\frac{160-64x+(4K+26)/p}{27}.
\tag{7}
\]
For \(97/64\le x\le13/8\) and \(K\ge266\), this gives
\[
2<\frac{2d}{p}<\frac{64}{27}<3.
\tag{8}
\]
Every odd source band is
\[
[6\cdot2^k+1,\ 8\cdot2^k-1].
\]
For \(k\le K-2\), its upper endpoint is at most \(2p-1\); for \(k\ge K-1\), its lower endpoint is at least \(3p+1\). Equation (8) puts \(2d\) strictly between these bands. Hence no odd parent exists. The previous theorem already gives \(4p<E<6p-1\), so \(E\) has no even parent either. This proves (3).

For \(a\bmod54\in S_0\), the table only gives \(27\mid X\); valuations \(v_3(X)\ge3\) remain possible and are not excluded here.

## 2. The \(X\equiv3\pmod9\) phase: a forced two-edge parent chain ends in a gap

Now \(K\equiv48-3a\pmod{54}\). Let \(d=X/3\) and let
\[
h=2d-4p-K-4.
\tag{9}
\]
The preceding theorem proves that \(E\) has no even parent and has exactly one odd parent, namely \(h\) at scale \(K-1\). In this phase \(h\equiv2\pmod3\), so an odd parent of \(h\) is arithmetically possible.

To determine its next valuation, compute \(X\) modulo \(27\) from the numerator in (7) modulo \(81\). The order of \(2\) modulo \(81\) is \(54\), so the answer depends on \(a\bmod54\). The resulting exact table, expressed as a partition, is
\[
\begin{array}{c|l}
h\bmod9 & a\bmod54\\ \hline
2 &
1,3,5,17,31,33,43,45,47\\
5 &
7,9,11,19,21,23,35,49,51\\
8 &
13,15,25,27,29,37,39,41,53.
\end{array}
\tag{10}
\]
If \(a\bmod54\notin S_3\), then \(h\bmod9\) is \(5\) or \(8\). Therefore
\[
Y:=2h+5\equiv6\ \text{or}\ 3\pmod9,
\]
so \(v_3(Y)=1\). Its only possible odd-parent parameter is
\[
g=Y/3.
\]
Substitution from (7) and (9) gives the exact normalized expression
\[
\frac gp=\frac{248-128x}{27}+\frac{25-10K}{27p}.
\tag{11}
\]

For \(x\in\mathcal W\), equation (11) gives
\[
\frac32<\frac gp<2.
\tag{12}
\]
For the lower bound, \(x\le415/256-1/1024\) makes
\(248-128x\ge325/8\), and \(p/8>10K\) for \(K\ge266\).
For the upper bound, \(x\ge803/512\) gives
\(248-128x\le189/4\), while the correction in (11) is negative.
Since \(g\) is odd, (12) puts it in the unique odd source band at scale \(K-2\):
\[
6\cdot2^{K-2}+1\le g\le8\cdot2^{K-2}-1.
\]
Thus \(h\) has exactly one odd parent, at that scale:
\[
G=2g-2p-K-3.
\tag{13}
\]

Combining (11) and (13),
\[
\frac Gp=\frac{442-256x}{27}-\frac{47K+31}{27p}.
\tag{14}
\]
The lower endpoint of \(\mathcal W\) gives
\(442-256x\le81/2\), hence \(G<3p/2\).
The upper endpoint gives \(442-256x\ge109/4\), and
\(p/4>47K+31\) for \(K\ge266\), hence \(G>p\).
Therefore
\[
p<G<\frac{3p}{2}.
\tag{15}
\]
The adjacent even-parent bands are
\[
[3p/4-1,\ p-3]\quad\text{at scale }K-3,
\qquad
[3p/2-1,\ 2p-3]\quad\text{at scale }K-2.
\]
Equation (15) places \(G\) strictly in the gap between them, so \(G\) has no even parent.

It remains to exclude odd parents of \(G\). If \(h\equiv5\pmod9\), then \(g\equiv2\pmod3\); if \(h\equiv8\pmod9\), then \(g\equiv1\pmod3\). Since \(p\equiv2\pmod3\) and \(K\equiv0\pmod3\), equation (13) gives
\[
G\equiv2g-2p-K-3\equiv0\ \text{or}\ 1\pmod3.
\]
Every odd ResetParent target is \(2\bmod3\), so \(G\) has no odd parent. Thus \(G\) is parentless, \(h\) has exactly one parent \(G\), and \(E\) has exactly one parent \(h\). No finite ResetParent chain from \(2\) can end at \(E\). This proves (4).

For \(a\bmod54\in S_3\), the table gives \(h\equiv2\pmod9\), so \(9\mid2h+5\); higher odd valuations remain possible and this two-edge closure does not apply.

## 3. Nonvacuity and exact remaining scope

The width of \(\mathcal W\) as a \(K\)-interval is \(53\cdot2^a/2048\), which exceeds \(54\) for every odd \(a\ge13\). Thus every allowed K residue class, including the two exceptional phases, occurs inside the subwindow.

The two exceptional lift sets intersect in
\[
S_0\cap S_3=\{3,5,47\}.
\]
For \(a\bmod54\) outside \(S_0\cup S_3\), both former exceptional phases are closed throughout \(\mathcal W\), while the other seven phases were already closed throughout the wider interval. Hence all nine t=0 phases are root-excluded in \(\mathcal W\) for the 12 classes in (5).

The remaining work is now sharply localized:
- \(a\bmod54\in S_0\): the \(X\equiv0\pmod9\) branch has \(27\mid X\), so \(t\ge2\) remains possible;
- \(a\bmod54\in S_3\): the \(X\equiv3\pmod9\) branch has \(9\mid2h+5\), so a higher-valuation parent of \(h\) remains possible;
- outside \(\mathcal W\), the \(X\equiv3\pmod9\) branch is not covered by the gap argument;
- none of these auxiliary-entry results excludes other odd side branches leaving earlier spine nodes or proves the actual fatal target unreachable.

This is a conditional t=0 branch reduction for #746, not a machine nonhalting theorem or a BB(6) solution. The exact finite lift tables are checked by t0_odd_a_k3_second_lift.mjs; the interval and parent-chain arguments are separate exact proofs.
