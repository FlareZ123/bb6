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
\alpha_j=2^{V_{j-3}-T_j}-2\quad(j=3,4,5,6),
\]
and
\[
\alpha_j=2^{\,T_j^{\,\alpha_{j-2}+1}-T_j+1}-2
\quad(j\ge7).
\]
Define the upper exponents by
\[
\gamma_j=2^{T_{j+1}-T_j}-2^{V_{j-3}-T_j}\quad(j\ge3).
\]
The lower inequality establishes \(V_{j-3}>T_j\), while the elementary upper comparison gives \(V_{j-3}<T_{j+1}\); hence these are positive integers. In particular, \(\gamma_3=2^{65520}-2^{47}\).

For every \(j\ge3\),
\[
\boxed{
T_{j+3}^{\,T_{j+2}^{\,\alpha_j}}<V_j
\qquad\text{and}\qquad
V_j^{\,T_{j+2}^{\,\gamma_j}}<T_{j+4}.
}
\]
The lower exponent uses an exact divisibility lift with a two-index recurrence. The upper exponent is the exact congruence-limited exponent obtained from \(V_{j-2}=2^{V_{j-3}}-1\).

These bounds uniformly strengthen the earlier fixed exponents: \(\alpha_j>2^{46}\) and \(\gamma_j>2^{65518}\) for every \(j\ge3.

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

Use the exact divisibility lift for any \(j\ge3\) with \(V_{j-3}>T_j\). Put
\[
m=2^{V_{j-3}-T_j}\ge2.
\]
Since \(T_{j+1}=2^{T_j}\),
\[
V_{j-2}=2^{V_{j-3}}-1=T_{j+1}m-1,
\]
and hence
\[
V_{j-1}=2^{T_{j+1}m-1}-1.
\]
For \(\alpha=m-2\),
\[
T_{j+2}^{\alpha+1}
=2^{T_{j+1}(m-1)}
<2^{T_{j+1}m-1}-1
=V_{j-1},
\]
because the two exponents differ by \(T_{j+1}-1\ge1\). Therefore
\[
T_{j+3}^{\,T_{j+2}^{\,\alpha}}
=2^{T_{j+2}^{\alpha+1}}
<2^{V_{j-1}}-1
=V_j.
\]
Thus every integer \(\alpha\le2^{V_{j-3}-T_j}-2\) is valid, and the next integer \(m-1\) fails because \(T_{j+2}^{m}=2^{T_{j+1}m}>V_{j-1}\). Hence \(m-2\) is maximal for this exact congruence lift.

The condition \(V_{j-3}>T_j\) holds for \(j=3,4,5,6\). For \(j=3\), \(V_0=63>T_3=16\). For \(j=4,5,6\), in fact \(V_k>T_{k+3}+47\) for every \(k\ge1\): the base is \(V_1=2^{63}-1>T_4+47\), and if \(V_k>T_{k+3}+47\), integrality gives \(V_k\ge T_{k+3}+48\), whence
\[
V_{k+1}=2^{V_k}-1\ge2^{T_{k+3}+48}-1>T_{k+4}+47.
\]
This proves the four direct bases \(\alpha_j=2^{V_{j-3}-T_j}-2\), including \(\alpha_3=2^{47}-2\), and gives \(\alpha_j>2^{46}\) there.

For \(j\ge7\), the induction hypothesis at index \(j-2\) gives
\[
V_{j-2}>T_{j+1}^{\,T_j^{\,\alpha_{j-2}}}.
\]
Since \(2^{V_{j-3}}=V_{j-2}+1>T_{j+1}^{\,T_j^{\,\alpha_{j-2}}}\), taking logarithms yields
\[
V_{j-3}>
\log_2\!\left(T_{j+1}^{\,T_j^{\,\alpha_{j-2}}}\right)
=T_j^{\,\alpha_{j-2}+1}>T_j.
\]
Since the quantities are integers, \(V_{j-3}\ge T_j^{\,\alpha_{j-2}+1}+1\). The exact lift therefore applies, and the defined exponent
\[
\alpha_j=2^{\,T_j^{\,\alpha_{j-2}+1}-T_j+1}-2
\]
is no larger than \(2^{V_{j-3}-T_j}-2\). Also \(T_j^{\alpha_{j-2}+1}\ge T_j^2\), so \(\alpha_j>2^{46}\). This proves the lower inequality for all \(j\ge3\).

### Upper inequality

Fix \(j\ge3\), and put
\[
Y=T_{j+1}=2^{T_j},\qquad X=T_{j+2}=2^Y.
\]
The lower inequality gives \(V_{j-3}>T_j\), and the elementary upper comparison gives \(V_{j-3}<T_{j+1}=Y\). Thus \(2^{V_{j-3}}\) is divisible by \(Y\), and
\[
\gamma_j
=2^{Y-T_j}-2^{V_{j-3}-T_j}
=\frac{X-2^{V_{j-3}}}{Y}
\]
is a positive integer. In particular,
\[
X^{\gamma_j}=2^{Y\gamma_j}
=2^{X-2^{V_{j-3}}}.
\]

The recurrence gives
\[
V_{j-2}=2^{V_{j-3}}-1,\qquad
V_{j-1}=2^{\,2^{V_{j-3}}-1}-1
<2^{\,2^{V_{j-3}}}.
\]
Using \(V_j<2^{V_{j-1}}\), we obtain
\[
\begin{aligned}
V_j^{X^{\gamma_j}}
&<2^{V_{j-1}X^{\gamma_j}}\\
&<2^{\,2^{2^{V_{j-3}}}\,2^{X-2^{V_{j-3}}}}\\
&=2^{2^X}
=T_{j+4}.
\end{aligned}
\]
For \(j\ge4\), write \(k=j-3\ge1\). The elementary upper comparison gives \(V_{k-1}<T_{k+3}=T_j\), hence
\[
V_{j-3}=2^{V_{j-4}}-1
\le2^{T_j-1}-1
=\frac{Y}{2}-1.
\]
Consequently
\[
\gamma_j
=2^{Y-T_j}\left(1-2^{V_{j-3}-Y}\right)
>2^{Y-T_j-1}>2^{65518},
\]
since \(Y-T_j-1\ge T_5-T_4-1=2^{65536}-65537>65518\). The case \(j=3\) is the explicit value \(\gamma_3=2^{65520}-2^{47}>2^{65518}\).

This proves the upper inequality for every \(j\ge3\). The exponent is maximal for this integer product-budget argument: the bound \(V_{j-1}<2^{2^{V_{j-3}}}\) leaves \(X-2^{V_{j-3}}\) as the largest multiple of \(Y\) available for \(Y\gamma_j\).

## Conditional score consequence

Here \(q=M+N+50\) is the source-dossier index, with the linked score expansion's hypotheses \(N\ge256\), \(3\mid N\), \(U\le R\), and root parameter \(R\ge63\). Use the source-dossier identities
\[
b_N=V_{q-4},\qquad
\ell=\log_2(b_N+1)=V_{q-5},
\qquad b_N+1=2^\ell.
\]
For \(q\ge8\), put
\[
L_b=T_{q-1}^{\,T_{q-2}^{\,\alpha_{q-4}}},
\qquad
L_\ell=T_{q-2}^{\,T_{q-3}^{\,\alpha_{q-5}}},
\qquad
B=\max\{L_b+2,\ 2^{L_\ell+1}\}.
\]
The lower recurrence inequalities at \(j=q-4\) and \(j=q-5\), together with integrality, give
\[
b_N+1\ge L_b+2,\qquad
\ell\ge L_\ell+1.
\]
Using \(b_N+1=2^\ell\) also gives \(b_N+1\ge2^{L_\ell+1}\), so \(b_N+1\ge B\).

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
Substitution gives the sharper conditional score interval
\[
\boxed{
6B^2+42B+3(L_\ell+1)
\le
S_{\rm TM1}
<
6\cdot2^{2\ell}+42\cdot2^\ell+3\ell
+10(1+\log_2\ell)\ell^2.
}
\]
The upper endpoint uses the exact identity \(b_N+1=2^\ell\), rather than a much looser tower root. The entire interval remains conditional on the authentic root/dispatcher source composition and the exact score decomposition; neither has passed the full local compile/axiom gate.

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
Also \(N>2^A\) and \(q-1>N\). Since the conditional score lower bound gives \(S_{\rm TM1}>T_{q-1}\), monotonicity of \(T\) yields
\[
\boxed{
S_{\rm TM1}>
T_{\,
2^{\,T_{M+45}^{\,T_{M+44}^{\,\alpha_{M+42}}}}
}.
}
\]
This strictly improves the earlier fixed-\(2^{46}\) outer-tower endpoint because the strengthened lower sequence satisfies \(\alpha_j>2^{46}\) for every \(j\ge3\).

## Validation boundary and next action

- The displayed inequalities are mathematical derivations about the scalar recurrence \(V_{j+1}=2^{V_j}-1\), with explicit base cases and induction/direct comparison arguments.
- The existing TM63TowerRecurrence.lean checks the weaker fixed-exponent \(23/8,4092\) sandwich. This moving-exponent result has **not** yet been encoded or compiled.
- The score substitution depends on the source-level TM63 route and exact score decomposition. The existing theorem sectionResult_run_complete has an exact run tm2 (sectionResult.cost) result type, assembled from the per-class source run theorems. If its full import closure compiles and passes the transitive axiom audit, it proves that proposedIncrementCost is the primitive TM2 run length for the complete countdown. Until that acceptance gate passes, the authentic blank-root orbit and exact score remain conditional.
- Next formalization target: encode the exact congruence lower lift and the V-dependent upper exponent \(\gamma_j=2^{T_{j+1}-T_j}-2^{V_{j-3}-T_j}\) in a separate module importing TM63TowerRecurrence. Then obtain a local Lean 4.36.0-rc2 preflight of the exact source closure and inspect exported axiom profiles before updating any score synthesis.
