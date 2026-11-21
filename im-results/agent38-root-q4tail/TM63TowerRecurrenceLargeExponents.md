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
and the upper denominator sequence by
\[
d_2=65473,\qquad D_k=2^{d_k},\qquad
 d_{k+1}=T_{k+3}-2^{T_{k+2}-d_k}-1\quad(k\ge2),
\]
with upper exponents
\[
\gamma_j=2^{T_{j+1}-T_j}-2^{T_{j+1}-T_j-d_{j-1}}\quad(j\ge3).
\]
In particular, \(\gamma_3=2^{65520}-2^{47}\). All these exponents are positive integers.

For every \(j\ge3\),
\[
\boxed{
T_{j+3}^{\,T_{j+2}^{\,\alpha_j}}<V_j
\qquad\text{and}\qquad
V_j^{\,T_{j+2}^{\,\gamma_j}}<T_{j+4}.
}
\]
The lower exponent is recursively amplified at each step. The upper exponent uses the recursively shrinking relative headroom \(1/D_{j-1}\).

These bounds strictly strengthen the earlier fixed exponents \(2^{46}\) and \(2^{65518}\). In particular, \(\alpha_3>2^{46}\) and \(\gamma_3>2^{65518}\).

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

### Upper inequality

We first establish
\[
1\le d_k\le T_{k+2}-T_{k+1}\qquad(k\ge2).
\]
The base case is \(65473\le T_4-T_3=65520\). If the bound holds at \(k\), then
\[
T_{k+2}-d_k\ge T_{k+1},
\]
so
\[
T_{k+2}\le2^{T_{k+2}-d_k}\le2^{T_{k+2}-1}=T_{k+3}/2.
\]
Substitution in the definition of \(d_{k+1}\) gives
\[
1\le d_{k+1}\le T_{k+3}-T_{k+2}.
\]
Moreover,
\[
d_{k+1}\ge T_{k+3}/2-1>T_{k+2}>d_k,
\]
so \(D_k\) strictly increases. In particular, \(D_k\) divides \(T_{k+3}\), and \(D_{k+1}\) divides \(T_{k+4}\).

Next prove the auxiliary bound
\[
V_k<T_{k+4}^{1/D_k}\qquad(k\ge2).
\]
At \(k=2\),
\[
T_6^{1/D_2}
=2^{\,2^{65536}/2^{65473}}
=2^{2^{63}}
>V_2.
\]
For the induction, put \(t=T_{k+4}=2^{T_{k+3}}\). Divisibility gives
\[
t^{1/D_k}=2^{T_{k+3}/D_k}
=2^{2^{T_{k+2}-d_k}}.
\]
By the definition of \(d_{k+1}\),
\[
t/D_{k+1}
=2^{T_{k+3}-d_{k+1}}
=2^{2^{T_{k+2}-d_k}+1}
=2t^{1/D_k}.
\]
Thus, if \(V_k<t^{1/D_k}\), then
\[
V_{k+1}=2^{V_k}-1
<2^{t^{1/D_k}}
<2^{t/D_{k+1}}
=T_{k+5}^{1/D_{k+1}}.
\]
This proves the auxiliary estimate.

Now fix any \(j\ge3\), and put
\[
Y=T_{j+1}=2^{T_j},\qquad X=T_{j+2}=2^Y.
\]
Since \(j-1\ge2\), the auxiliary estimate gives
\[
V_{j-1}<T_{j+3}^{1/D_{j-1}}=2^{X/D_{j-1}}.
\]
The invariant on \(d_{j-1}\) ensures that the exponent in
\[
\gamma_j
=2^{Y-T_j}-2^{Y-T_j-d_{j-1}}
\]
is a nonnegative integer. It satisfies
\[
Y\gamma_j
=2^Y-2^{Y-d_{j-1}}
=X-X/D_{j-1},
\]
and therefore
\[
X^{\gamma_j}=2^{X-X/D_{j-1}}.
\]
Using \(V_j<2^{V_{j-1}}\), we obtain
\[
\begin{aligned}
V_j^{X^{\gamma_j}}
&<2^{V_{j-1}X^{\gamma_j}}\\
&<2^{\,2^{X/D_{j-1}}\,2^{X-X/D_{j-1}}}\\
&=2^{2^X}
=T_{j+4}.
\end{aligned}
\]
This proves the upper inequality for every \(j\ge3\).

## Conditional score consequence

Use the source-dossier identities
\[
b_N=V_{q-4},\qquad
\ell=\log_2(b_N+1)=V_{q-5}.
\]
For \(q\ge8\), put
\[
L_b=T_{q-1}^{\,T_{q-2}^{\,\alpha_{q-4}}},
\qquad
L_\ell=T_{q-2}^{\,T_{q-3}^{\,\alpha_{q-5}}},
\]
\[
E=T_{q-2}^{\,\gamma_{q-4}},
\qquad
D=D_{q-5},
\qquad
H=2^{\,T_{q-2}/D},
\qquad
U=2^H.
\]
The lower recurrence inequalities at \(j=q-4\) and \(j=q-5\) give
\[
L_b<b_N,\qquad L_\ell<\ell.
\]
For the upper side, the \(j=q-4\) exponent identity gives
\[
E=T_{q-2}^{\gamma_{q-4}}
=2^{T_{q-2}-T_{q-2}/D},
\qquad
\frac{T_{q-1}}{E}=2^{T_{q-2}/D}=H.
\]
All exponents are integers by the divisibility invariant for \(D_{q-5}\). Hence
\[
U^E=2^{HE}=2^{T_{q-1}}=T_q.
\]
The upper recurrence inequality \(b_N^E<T_q\) therefore gives
\[
b_N<U,\qquad b_N+1\le U,\qquad \ell\le H.
\]

The exact source-conditional score expansion in
[TM63ScoreAsymptotic.md](../agent42-q4-s0-drain/TM63ScoreAsymptotic.md) is
\[
S_{\rm TM1}
=6(b_N+1)^2+42(b_N+1)+3\ell+\Delta,
\]
where
\[
0\le\Delta<10(1+\log_2\ell)\ell^2.
\]
Substituting the moving lower and upper bounds yields the sharper conditional interval
\[
\boxed{
6(L_b+2)^2+42(L_b+2)+3(L_\ell+1)
\le
S_{\rm TM1}
<
6U^2+42U+3H+10(1+\log_2 H)H^2.
}
\]
This retains the exact final counted-increment linear term and the explicit polylogarithmic remainder, rather than replacing the score by the coarser \(6b_N^2<S_{\rm TM1}<9b_N^2\). The entire interval remains conditional on the authentic root/dispatcher source composition and the exact score decomposition; neither has passed the full local compile/axiom gate.

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
