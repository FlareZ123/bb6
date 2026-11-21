# Odd-a K ≡ 3 (mod 6): third-lift 79-of-81 exclusion

**Status:** exact paper-level continuation of the seven-of-nine and corrected K-mod-162 reductions. The new lift law is algebraic; the finite residue reproducer checks its application to every odd \(a\bmod162\). The dyadic source-gap inequalities are exact. No Lean compilation has yet been completed; keep this in im-results.

## Theorem

Let \(a\ge15\) be odd, \(K\equiv3\pmod6\), and
\[
x=\frac{2K+7}{2^a}\in
\mathcal W=
\left[\frac{803}{512},\frac{415}{256}-\frac1{1024}\right].
\tag{1}
\]
Use the auxiliary t=0 entry \(E\), \(X=2E+5\), and the two exceptional K-mod-54 phases from the preceding notes. The interval \(\mathcal W\) has K-width
\[
\frac{53\cdot2^a}{2048}>486
\qquad(a\ge15),
\tag{2}
\]
so all three lifts modulo \(486\) of each residue modulo \(162\) occur.

The first theorem excludes all three K-mod-162 lifts of seven of the nine K-mod-54 phases. The second-lift theorem leaves one high-valuation K-mod-162 class in each of the two exceptional phases. This theorem shows that, in each such high class, two of its three K-mod-486 lifts are also root-excluded. Consequently, for every fixed odd \(a\ge15\), **79 of the 81 K-mod-486 classes** satisfying \(K\equiv3\pmod6\) are excluded for the auxiliary entry \(E\). Exactly two higher-valuation classes remain, one in each exceptional phase.

## 1. The exact 162-shift law

Recall
\[
T(K)=80\cdot2^K+2K+13
-2(2K+7)2^{K+4-a},
\qquad X(K)=T(K)/3.
\tag{3}
\]
Put \(e=K+4-a\). Since \(K\) and \(a\) are odd, \(e\) is even. Also
\[
2^{162}\equiv1\pmod{243}.
\]
For the shift \(K\mapsto K+162\), both powers of two in (3) are unchanged modulo \(243\), while the linear factors change by \(324\). Hence
\[
\begin{aligned}
T(K+162)-T(K)
&\equiv324-648\cdot2^e\\
&\equiv81(1-2\cdot2^e)
\equiv162\pmod{243},
\end{aligned}
\]
because \(2^e\equiv1\pmod3\). Dividing by three gives
\[
\boxed{X(K+162)\equiv X(K)+54\pmod{81}.}
\tag{4}
\]

For the \(X\equiv3\pmod9\) phase, let
\[
h(K)=2(X(K)/3)-4\cdot2^K-K-4,\qquad
Y(K)=2h(K)+5.
\]
Using (4), \(2^{K+162}\equiv2^K\pmod{27}\), and \(324\equiv0\pmod{27}\), we obtain
\[
\boxed{Y(K+162)\equiv Y(K)+18\pmod{27}.}
\tag{5}
\]

## 2. The high \(X\equiv0\pmod9\) phase loses two of three K-mod-486 lifts

By the corrected second-lift theorem, for each fixed \(a\) there is exactly one high K-mod-162 class in the phase
\[
K\equiv12-3a\pmod{54}
\]
for which \(27\mid X\). Let \(K_*\) represent that class modulo \(162\). Equation (4) shows that the three lifts
\[
K_*,\quad K_*+162,\quad K_*+324\pmod{486}
\]
have \(X\bmod81\) equal to \(0,27,54\) in some order. Thus two lifts have
\[
v_3(X)=3
\]
exactly. For either such lift, the odd ResetParent exponent is forced to be \(t=2\), with odd parameter \(d=X/27\) and source-band parameter \(4d\).

The exact normalized source parameter is
\[
\frac{4d}{p}
=\frac{4(80-32x+(2K+13)/p)}{81}.
\tag{6}
\]
For \(x\in\mathcal W\),
\[
\frac{901}{648}
<
\frac{4(80-32x)}{81}
\le\frac{53}{36}.
\]
Since \(2K+13<p/2\) for \(K\ge266\), the correction in (6) is less than \(2/81\). Therefore
\[
1<\frac{4d}{p}
<
\frac{53}{36}+\frac{2}{81}
<\frac32.
\tag{7}
\]
The odd source bands adjacent to this interval end at \(p-1\) and begin at \(3p/2+1\), so \(4d\) lies in the strict gap \((p,3p/2)\). There is no odd parent of \(E\); the preceding theorem already excludes even parents of \(E\). Both lifts with \(v_3(X)=3\) are therefore root-excluded. The unique lift with \(X\equiv0\pmod{81}\) has \(v_3(X)\ge4\) and remains open.

## 3. The high \(X\equiv3\pmod9\) phase also loses two of three K-mod-486 lifts

By the corrected second-lift theorem, for each fixed \(a\) there is exactly one high K-mod-162 class in the phase
\[
K\equiv48-3a\pmod{54}
\]
for which \(9\mid Y=2h+5\). Let \(K^\dagger\) represent that class modulo \(162\). Equation (5) shows that the three lifts
\[
K^\dagger,\quad K^\dagger+162,\quad K^\dagger+324\pmod{486}
\]
have \(Y\bmod27\) equal to \(0,9,18\) in some order. Thus two lifts have
\[
v_3(Y)=2
\]
exactly. For either such lift, the odd ResetParent exponent of \(h\) is forced to be \(t=1\), with odd parameter \(g=Y/9\) and source-band parameter \(2g\).

From the preceding derivation,
\[
\frac{2g}{p}
=\frac{2(248-128x)}{81}+\frac{50-20K}{81p}.
\tag{8}
\]
On \(\mathcal W\), the first term is between \(325/324\) and \(7/6\). Since \(80K<p\) for \(K\ge266\), the negative correction has magnitude less than \(1/324\). Hence
\[
1<\frac{2g}{p}<\frac76<\frac32.
\tag{9}
\]
This is the strict odd-source gap \((p,3p/2)\), between the scale-\((K-3)\) and scale-\((K-2)\) bands. Thus \(h\) has no odd parent. The preceding theorem already puts \(h\) in an even-parent gap, and \(E\) has \(h\) as its unique parent in this phase. Consequently \(E\) is root-excluded in both lifts with \(v_3(Y)=2\). The unique lift with \(Y\equiv0\pmod{27}\) has \(v_3(Y)\ge3\) and remains open.

## 4. Combined count and scope

There are \(9\) K-mod-54 phases and \(3\) K-mod-486 lifts of each, for \(81\) classes total. The seven nonexceptional phases contribute \(7\cdot9=63\) excluded classes. In each exceptional phase:
- the second-lift theorem excludes \(2\) of the \(3\) K-mod-162 lifts;
- the shift law and (7) or (9) exclude \(2\) of the \(3\) K-mod-486 lifts of the remaining high class.

Thus each exceptional phase has \(8\) of its \(9\) K-mod-486 lifts excluded. The total is
\[
63+8+8=79
\]
excluded classes out of \(81\), leaving exactly two high-valuation classes.

The remaining classes are:
- one class with \(81\mid X\), where the next odd exponent is at least \(t=3\);
- one class with \(27\mid Y\), where the next odd exponent is at least \(t=2\).

This is a conditional inverse-parent reduction for the auxiliary t=0 entry \(E\). It does not exclude the two remaining higher-valuation classes, other odd side branches leaving earlier fatal-spine nodes, or the fatal target itself. It is not a proof about BB(6).

The accompanying t0_odd_a_k3_third_lift.mjs checks the 162-shift residues and the resulting three-lift partitions for all odd \(a\bmod162\). The shift identities (4)–(5) are algebraic; the dyadic gap inequalities are separate exact arguments.
