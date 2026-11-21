# Larger moving exponents for the TM63 tower recurrence

**Status:** new paper-level recurrence lemma; not yet Lean-compiled. This strengthens the already checked scalar recurrence sandwich. It does **not** establish the authentic TM63 itinerary or an unconditional BB(6) bound.

## Statement

Let
\[
T_1=2,\qquad T_{n+1}=2^{T_n},
\]
and
\[
V_0=63,\qquad V_{j+1}=2^{V_j}-1.
\]
For every integer \(j\ge 3\), the following stronger moving-exponent inequalities hold:
\[
\boxed{\quad
T_{j+3}^{\,T_{j+2}^{\,2^{46}}}<V_j
\quad\text{and}\quad
V_j^{\,T_{j+2}^{\,2^{65518}}}<T_{j+4}.
\quad}
\]
The constants are deliberately simple powers of two with comfortable slack; they are not claimed optimal.

For the source-conditional score application already derived in [TM63PublishedTowerSandwich.md](../agent42-q4-s0-drain/TM63PublishedTowerSandwich.md), let \(b_N=V_{q-4}\), with \(q-4\ge3\). The exact terminal-summand estimate in [DirectTerminalTetrationBound.md](../agent24-champion-time/DirectTerminalTetrationBound.md) gives \(S\ge6(b_N+1)^2\), while the global decomposition gives \(S<9b_N^2\). Thus
\[
\boxed{\quad
6\bigl(T_{q-1}^{\,T_{q-2}^{\,2^{46}}}+1\bigr)^2
<S<
9T_q^{\,2/T_{q-2}^{\,2^{65518}}}.
\quad}
\]
This is a strict strengthening of the earlier recurrence exponents \(23/8\) and \(4092\), with the lower bound also retaining the exact final-summand \(+1\). It remains conditional on the uncompiled authentic source-to-terminal composition and the exact score decomposition.
## Proof of the recurrence inequalities

Write \(\alpha=2^{46}\) and \(C=2^{65518}\).

### Base case \(j=3\)

The initial values are
\[
T_4=2^{16}=65536,\quad T_5=2^{65536},\quad
T_6=2^{T_5},\quad T_7=2^{T_6},
\]
\[
V_1=2^{63}-1,\quad V_2=2^{V_1}-1,\quad V_3=2^{V_2}-1.
\]

For the lower bound,
\[
T_5^{\alpha+1}
=2^{65536(2^{46}+1)}
=2^{2^{62}+2^{16}}.
\]
Put \(e=2^{62}+2^{16}\). Since \(e+3\le V_1=2^{63}-1\), comparison of powers gives \(2^{e+1}<2^{V_1}-1=V_2\), hence \(2^e+2\le V_2\). Therefore
\[
T_6^{T_5^\alpha}
=2^{2^e}
<2^{V_2}-1
=V_3.
\]

For the upper bound,
\[
T_5^C=2^{65536\cdot2^{65518}}=2^{2^{65534}}.
\]
Since \(V_2<2^{2^{63}}\) and \(2^{63}+2^{65534}<2^{65536}\),
\[
V_2T_5^C
<2^{2^{63}+2^{65534}}
<2^{2^{65536}}
=T_6.
\]
Using \(V_3<2^{V_2}\),
\[
V_3^{T_5^C}
<2^{V_2T_5^C}
<2^{T_6}=T_7.
\]

### Lower induction step

Assume
\[
X^{Y^\alpha}<V_j,
\qquad X=T_{j+3}=2^Y,\quad Y=T_{j+2}.
\]
Because \(Y\ge2\) and \(\alpha\ge2\), \(Y^\alpha\ge\alpha+2\). Hence
\[
X^{Y^\alpha}>X^{\alpha+1}+1.
\]
The recurrence gives
\[
T_{j+4}^{T_{j+3}^\alpha}
=(2^X)^{X^\alpha}
=2^{X^{\alpha+1}}
<2^{X^{Y^\alpha}}-1
<2^{V_j}-1
=V_{j+1}.
\]
This is the required lower inequality at \(j+1\).

### Upper induction step

First note the elementary bound
\[
V_k<T_{k+4}\qquad(k\ge0).
\]
It holds at \(k=0\), since \(63<T_4\), and is preserved by \(V_{k+1}=2^{V_k}-1\) and \(T_{k+5}=2^{T_{k+4}}\).

For \(j\ge3\), put \(Y=T_{j+2}\) and \(X=T_{j+3}=2^Y\). The elementary bound gives
\[
V_{j-2}<Y,
\]
so, using integrality twice,
\[
V_{j-1}<2^{Y-1}=X/2,
\qquad
V_j<2^{X/2}.
\]
Also \(Y\ge T_5=2^{65536}\), hence \(C\le Y\). For \(Y\ge8\), \(Y^2<2^{Y-1}\) (base case \(Y=8\), then induction using \((Y+1)^2\le2Y^2\)). Therefore
\[
CY\le Y^2<2^{Y-1}=X/2,
\qquad
X^C=2^{CY}<2^{X/2}.
\]
Multiplying the two strict bounds gives
\[
V_jX^C<2^X.
\]
Now
\[
V_{j+1}^{X^C}
<2^{V_jX^C}
<2^{2^X}
=T_{j+5},
\]
which is the required upper inequality at \(j+1\).

This completes the induction.

## Score substitution

Take \(j=q-4\). Then \(T_{j+3}=T_{q-1}\), \(T_{j+2}=T_{q-2}\), and \(T_{j+4}=T_q\), so
\[
T_{q-1}^{T_{q-2}^{2^{46}}}<b_N,
\qquad
b_N^{T_{q-2}^{2^{65518}}}<T_q.
\]
Using the exact final-summand lower bound \(S\ge6(b_N+1)^2\) and the global upper \(S<9b_N^2\) gives the boxed score sandwich.

## Stronger explicit lower tower for the outer index

Use the existing source-dossier notation
\[
A=V_7+\sum_{j=8}^{M+42}V_j+\frac{5M+176}{3},
\qquad
N=(2^{78}-1)2^A-3,
\qquad
q=M+N+50.
\]
All summands in \(A\) are nonnegative, so \(A\ge V_{M+42}\). Applying the new lower recurrence inequality at \(j=M+42\) gives
\[
A\ge V_{M+42}>
T_{M+45}^{\,T_{M+44}^{\,2^{46}}}.
\]
Since \((2^{78}-1)2^A-3>2^A\) for these parameters,
\[
N>2^A>
2^{\,T_{M+45}^{\,T_{M+44}^{\,2^{46}}}},
\qquad q-1>N.
\]
The exact score sandwich \(S>T_{q-1}\) therefore yields the additional explicit lower bound
\[
\boxed{
S>
T_{\,2^{\,T_{M+45}^{\,T_{M+44}^{\,2^{46}}}}}.
}
\]
The existing source arithmetic gives \(M\ge62T_{10}-36\), hence \(M+45>T_{10}\). Thus \(X=T_{M+45}^{T_{M+44}^{2^{46}}}>T_{T_{10}}\), so \(2^X>T_{T_{10}}\) and \(T_{2^X}>T_{T_{T_{10}}}\). This is therefore a stronger human-readable tower lower bound than the previous coarse \(T_{T_{T_{10}}}\) endpoint, conditional on the same authentic source itinerary and exact score decomposition. The exact \(q\)-indexed sandwich remains stronger and should be preferred when its source hypotheses are available.

## Validation boundary and next action

- The derivation is a proof about the scalar recurrence, with explicit elementary base and induction steps.
- The existing Lean file [TM63TowerRecurrence.lean](TM63TowerRecurrence.lean) formally checks the weaker \(23/8,4092\) version. This stronger statement has not yet been encoded or compiled.
- The score substitution still depends on the source-level TM63 route and exact score decomposition; it is not an unconditional statement about \(S(6)\).
- Next: formalize the two \(j\ge3\) inequalities in a separate Lean module importing `TM63TowerRecurrence`, obtain a local Lean 4.36.0-rc2 preflight, and inspect the exported axiom profile before updating the score synthesis.
