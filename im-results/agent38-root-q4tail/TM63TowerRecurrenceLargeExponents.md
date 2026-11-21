# Dynamically growing exponents for the TM63 tower recurrence

**Status:** paper-level recurrence result; not yet Lean-compiled. This strengthens the earlier fixed-exponent sandwich, but remains a theorem about the scalar recurrence only. It does **not** establish the authentic TM63 itinerary or an unconditional BB(6) bound.

## Recurrences and main statement

Let
\[
T_1=2,\qquad T_{n+1}=2^{T_n},
\]
and
\[
V_0=63,\qquad V_{j+1}=2^{V_j}-1.
\]

Define the lower exponents by
\[
\alpha_3=2^{47}-2,\qquad
\alpha_{j+1}=T_{j+2}^{\alpha_j}-1\quad(j\ge3),
\]
and the upper exponents by
\[
\gamma_3=2^{65520}-2^{47},\qquad
\gamma_j=2^{T_{j+1}-T_j}-2^{T_{j+1}-T_j-65473}\quad(j\ge4).
\]
All these exponents are positive integers.

For every \(j\ge3\),
\[
\boxed{
T_{j+3}^{\,T_{j+2}^{\,\alpha_j}}<V_j
\qquad\text{and}\qquad
V_j^{\,T_{j+2}^{\,\gamma_j}}<T_{j+4}.
}
\]
The lower exponent is recursively amplified at each step. The upper exponent also grows with the tower index. For \(j\ge4\), it leaves only a relative \(2^{-65473}\) headroom in the upper product comparison.

These bounds strictly strengthen the earlier fixed exponents \(2^{46}\) and \(2^{65518}\). In particular, \(\alpha_3>2^{46}\), \(\gamma_3>2^{65518}\), and both moving exponents subsequently grow.

## Proof

First, the elementary comparison
\[
V_k<T_{k+4}\qquad(k\ge0)
\]
holds. At \(k=0\), \(63<T_4=65536\). If \(V_k<T_{k+4}\), then
\[
V_{k+1}=2^{V_k}-1<2^{T_{k+4}}=T_{k+5}.
\]

### Lower inequality

At \(j=3\),
\[
T_4=65536,\quad T_5=2^{65536},\quad
T_6=2^{T_5},
\]
and
\[
V_1=2^{63}-1,\quad V_2=2^{2^{63}-1}-1,\quad
V_3=2^{V_2}-1.
\]
Since \(\alpha_3+1=2^{47}-1\),
\[
T_5^{\alpha_3+1}
=2^{65536(2^{47}-1)}
=2^{2^{63}-2^{16}}
<V_2.
\]
The last strict inequality follows from \(2^{63}-2^{16}<2^{63}-1\), with ample integer separation. Therefore
\[
T_6^{T_5^{\alpha_3}}
=2^{T_5^{\alpha_3+1}}
\le 2^{V_2-1}
<2^{V_2}-1=V_3.
\]

For the induction step, suppose
\[
X^{Y^{\alpha_j}}<V_j,
\qquad X=T_{j+3}=2^Y,\quad Y=T_{j+2}.
\]
Put \(m=Y^{\alpha_j}\), so \(\alpha_{j+1}=m-1\). Then
\[
T_{j+4}^{\,T_{j+3}^{\,\alpha_{j+1}}}
=(2^X)^{X^{m-1}}
=2^{X^m}.
\]
The induction hypothesis gives \(X^m\le V_j-1\), hence
\[
2^{X^m}\le2^{V_j-1}<2^{V_j}-1=V_{j+1}.
\]
This proves the lower inequality for every \(j\ge3\).

### Upper inequality: base case

Set
\[
\gamma_3=2^{65520}-2^{47}.
\]
Then
\[
T_5^{\gamma_3}
=2^{65536\gamma_3}
=2^{2^{65536}-2^{63}}.
\]
Since \(V_2<2^{2^{63}-1}\),
\[
V_2T_5^{\gamma_3}
<2^{2^{63}-1}\,2^{2^{65536}-2^{63}}
=2^{2^{65536}-1}
<T_6.
\]
Using \(V_3<2^{V_2}\), it follows that
\[
V_3^{T_5^{\gamma_3}}
<2^{V_2T_5^{\gamma_3}}
<2^{T_6}=T_7.
\]

### Upper inequality: all \(j\ge4\)

Put \(D=2^{65473}\). First prove the auxiliary estimate
\[
V_k<T_{k+4}^{1/D}\qquad(k\ge2).
\]
At \(k=2\),
\[
T_6^{1/D}
=2^{\,2^{65536}/2^{65473}}
=2^{2^{63}}
>V_2.
\]
For the induction, let \(t=T_{k+4}\). We have \(t\ge T_6>D^2\), hence
\[
t^{1/D}<t/D.
\]
If \(V_k<t^{1/D}\), then
\[
V_{k+1}=2^{V_k}-1
<2^{t^{1/D}}
<2^{t/D}
=T_{k+5}^{1/D}.
\]
This proves the auxiliary estimate.

Now fix \(j\ge4\), and put
\[
Y=T_{j+1}=2^{T_j},\qquad X=T_{j+2}=2^Y.
\]
Since \(j-1\ge2\), the auxiliary estimate gives
\[
V_{j-1}<T_{j+3}^{1/D}=2^{X/D}.
\]
By the definition of \(\gamma_j\),
\[
\begin{aligned}
Y\gamma_j
&=2^{T_j}\left(2^{Y-T_j}-2^{Y-T_j-65473}\right)\\
&=2^Y-2^{Y-65473}\\
&=X-X/D.
\end{aligned}
\]
Consequently,
\[
X^{\gamma_j}=2^{X-X/D}.
\]
Using \(V_j<2^{V_{j-1}}\), we obtain
\[
\begin{aligned}
V_j^{X^{\gamma_j}}
&<2^{V_{j-1}X^{\gamma_j}}\\
&<2^{\,2^{X/D}\,2^{X-X/D}}\\
&=2^{2^X}
=T_{j+4}.
\end{aligned}
\]
This proves the upper inequality for every \(j\ge4\), completing the theorem.

## Conditional score consequence

Use the source-dossier notation
\[
b_N=V_{q-4}.
\]
For \(q\ge7\), the recurrence theorem gives
\[
T_{q-1}^{\,T_{q-2}^{\,\alpha_{q-4}}}
<b_N,
\qquad
b_N^{\,T_{q-2}^{\,\gamma_{q-4}}}<T_q.
\]
The existing exact terminal-summand estimates are
\[
S\ge6(b_N+1)^2,\qquad S<9b_N^2.
\]
Thus, writing \(E=T_{q-2}^{\gamma_{q-4}}\),
\[
\boxed{
6\bigl(T_{q-1}^{\,T_{q-2}^{\,\alpha_{q-4}}}+1\bigr)^2
<S<
9T_q^{\,2/E}.
}
\]
Here \(E\ge4\), and \(T_q^{1/2}>9\), so the upper endpoint is strictly below \(T_q\). This is a substantially tighter moving-exponent sandwich than the earlier constant-exponent form.

The score consequence remains conditional on the authentic source-to-terminal composition and the exact score decomposition. It is not an unconditional statement about \(S(6)\).

## Stronger explicit lower tower from the outer index

The source dossier defines
\[
A=V_7+\sum_{j=8}^{M+42}V_j+\frac{5M+176}{3},
\qquad
N=(2^{78}-1)2^A-3,
\qquad
q=M+N+50.
\]
For the dossier's parameters, \(A\ge V_{M+42}\). Applying the new lower recurrence inequality at \(j=M+42\) gives
\[
A>
T_{M+45}^{\,T_{M+44}^{\,\alpha_{M+42}}}.
\]
Also \(N>2^A\) and \(q-1>N\). Since the lower score estimate implies \(S>T_{q-1}\), monotonicity of \(T\) yields
\[
\boxed{
S>
T_{\,
2^{\,T_{M+45}^{\,T_{M+44}^{\,\alpha_{M+42}}}}
}.
}
\]
This strictly improves the earlier fixed-\(2^{46}\) outer-tower endpoint because \(\alpha_{M+42}\ge\alpha_3=2^{47}-2>2^{46}\).

## Validation boundary and next action

- The displayed inequalities are mathematical derivations about the scalar recurrence \(V_{j+1}=2^{V_j}-1\), with explicit base cases and induction/direct comparison arguments.
- The existing TM63TowerRecurrence.lean checks the weaker fixed-exponent \(23/8,4092\) sandwich. This moving-exponent result has **not** yet been encoded or compiled.
- The score substitution depends on the source-level TM63 route and exact score decomposition. It does not prove that the authentic blank-root orbit follows the recurrence, nor that the candidate cost equals the primitive TM2 run length.
- Next formalization target: encode \(\alpha_j\) and \(\gamma_j\) recursively/explicitly in a separate module importing TM63TowerRecurrence, then obtain a local Lean 4.36.0-rc2 preflight and inspect exported axiom profiles before updating any score synthesis.
