# Normalized positive-return map for BMO5 #754

This note records a dynamical-systems representation of the already formalized positive-return recurrence. It is an intermediate research model, not a nonhalting proof.

## Exact recurrence

Write (P_k=5\cdot 2^k). On a positive entry ((k,q)), let
[
a_k=1+\max\{r\ge 0:3^r q\le 2P_k-2\}.
]
The existing `positiveNext` definition gives
[
q_{k+1}=3^{a_k}q_k-2P_k+3
       =3^{a_k}q_k-10\cdot2^k+3,
]
provided the positive gate succeeds, (q_{k+1}\ge k+7). This is the ordinary one-band return. If the gate fails, the signed negative-phase macro must be used; the recurrence must not be extrapolated through that event.

Normalize by (u_k=q_k/2^k). Then, exactly,
[
u_{k+1}=\frac{3^{a_k}}2u_k-5+\frac{3}{2^{k+1}}.
]
The exponent selection is equivalent to
[
\frac{10-2^{1-k}}{3^{a_k}}
 < u_k\le
\frac{10-2^{1-k}}{3^{a_k-1}}.
]
Thus the finite-(k) branch boundaries converge exponentially to (10/3^a).

The gate condition at the next band is
[
u_{k+1}\ge\frac{k+7}{2^{k+1}}.
]
A failed positive gate is therefore a shrinking-target event near zero, with target interval
[
J_k=\left(0,\frac{k+7}{2^{k+1}}\right).
]
The direct terminal at this first negative entry is the special case positiveNext(k,q)=k+3, equivalently positiveProduct(k,q)=2P_k+k; other gate failures must be followed through the exact negative macro and can return to a later positive band.

## Limiting full-branch map

Ignoring the exponentially small finite-(k) corrections gives the autonomous map
[
T(u)=\frac{3^a}{2}u-5
\quad\text{for}\quad
\frac{10}{3^a}<u\le\frac{10}{3^{a-1}},
\qquad a=1,2,\ldots.
]
Each branch maps its interval onto ((0,10]), with slope (3^a/2\ge3/2). Its inverse branch is
[
T_a^{-1}(v)=\frac{2(v+5)}{3^a},
\qquad 0<v\le10.
]
The inverse-branch Jacobians sum to
[
\sum_{a=1}^{\infty}\frac{2}{3^a}=1.
]
Consequently the transfer operator fixes the constant density: Lebesgue measure on ((0,10]) is invariant under this limiting map.

For the limiting map, (|J_k|=(k+7)/2^{k+1}) is summable. Since (T) preserves Lebesgue measure, the first Borel--Cantelli lemma implies that for Lebesgue-almost every initial (u_0), the orbit (T^k(u_0)) enters (J_k) only finitely often. This is a generic-orbit statement, not a statement about the distinguished rational seed (u_0=8).

## What this does and does not establish

- The normalized recurrence and the full-branch limiting map are exact algebraic rewrites of the positive-return definitions.
- The limiting map has an invariant Lebesgue measure and a summable shrinking target.
- This suggests treating the #754 obstruction as a *specific-orbit shrinking-target problem*, rather than expecting a universal fixed-modulus invariant.
- It does **not** prove that (u_0=8) avoids every target. The exact recurrence is non-autonomous, the branch endpoints move, and a failed gate invokes the separate signed macro. The limiting Borel--Cantelli argument does not transfer automatically to that exact orbit.
- No new BB(6) upper bound or #754 nonhalting claim follows.

## Next mathematical work

1. Derive exact cylinder intervals for the itinerary of (u_0=8) under the limiting map and compare their distances to the shrinking targets.
2. Quantify how the (2^{-k}) branch-boundary and additive corrections affect cylinder distortion; do not assume global shadowing, since the map is expanding.
3. If an exact positive gate fails, compose the signed negative return map with the next positive episode and formulate a non-autonomous return-map version of the shrinking-target problem.

Relevant formal sources: `CapPositiveRepeat.lean`, `CapPositiveRepeatBound.lean`, `CapNegativeExit.lean`, `CapSieveCore.lean`, and the root-specific discussion in `README.md`.


## Exact affine itinerary identity

For a fixed positive-return exponent word \(a_0,\ldots,a_{n-1}\), put
\[
A_j=\sum_{r<j}a_r,\qquad C_0=D_0=0,
\]
with \(C_{j+1}=3^{a_j}C_j+2^j\) and \(D_{j+1}=3^{a_j}D_j+1\). The existing Lean theorem `CapExitWord.expansion` proves, for the exact recurrence,
\[
3^{A_n}q_0+3D_n=q_n+10C_n.
\]
For the #754 seed \(q_0=8\), division by \(3^{A_n}\) gives
\[
8=\sum_{j=1}^{n}\frac{10\cdot2^{j-1}-3}{3^{A_j}}+\frac{q_n}{3^{A_n}}.
\]
Thus \(q_n/3^{A_n}\) is the exact arithmetic gap between the seed and the partial itinerary expansion. In the limiting autonomous map, the cylinder for this word is the interval
\[
\left(\sum_{j=1}^{n}\frac{10\cdot2^{j-1}}{3^{A_j}},\quad
\sum_{j=1}^{n}\frac{10\cdot2^{j-1}}{3^{A_j}}+\frac{10\cdot2^n}{3^{A_n}}\right],
\]
while the exact non-autonomous affine composition has the \(-3/3^{A_j}\) corrections displayed in the seed identity. For the exact positive orbit, the intermediate branch and gate constraints further restrict the affine preimage; do not treat the unrestricted affine interval as the exact finite-\(k\) cylinder.

The remaining obstruction is now explicit: the distinguished seed's itinerary must keep the integer gap \(q_n\) above the moving linear threshold \(k+n+6\) at every positive return. The identity supplies an exact series/cylinder representation, but it does not by itself give the needed lower bound. This is the Diophantine shrinking-target problem to attack next.


## Infinite expansion of the relaxed #754 orbit

Let \(q_0=8\) and \(q_{n+1}=\operatorname{positiveNext}(n,q_n)\) be the relaxed arithmetic orbit (the Lean `positiveOrbit 0 8`). This sequence is defined even at indices where the actual machine would leave the positive gate; the actual machine follows it only up to the first failed gate. Put \(a_n=1+\operatorname{positiveCount}(n,q_n)\) and \(A_n=\sum_{r<n}a_r\). The existing Lean theorem `CapExitWord.expansion` gives
\[
3^{A_n}q_0+3D_n=q_n+10C_n,
\]
where \(C_0=D_0=0\), \(C_{n+1}=3^{a_n}C_n+2^n\), and \(D_{n+1}=3^{a_n}D_n+1\). For \(q_0=8\), this is
\[
8=\sum_{j=1}^{n}\frac{10\cdot2^{j-1}-3}{3^{A_j}}+\frac{q_n}{3^{A_n}}.
\]
Because \(A_n\ge n\) and the relaxed positive-orbit upper bound gives \(0<q_n\le10\cdot2^n-2\), the remainder tends to zero. Therefore
\[
8=\sum_{j=1}^{\infty}\frac{10\cdot2^{j-1}-3}{3^{A_j}}.
\]
The tail after \(n\) terms is exactly \(q_n/3^{A_n}\). The all-time positive-gate obligation for this seed is \(q_n\ge n+6\) for every \(n\), equivalently
\[
\sum_{j>n}\frac{10\cdot2^{j-1}-3}{3^{A_j}}
=\frac{q_n}{3^{A_n}}\ge\frac{n+6}{3^{A_n}}.
\]
The exponent word is greedily generated by the exact return rule, not chosen arbitrarily. This reframes the open problem as a lower bound on the tails of a particular nonstationary base-3 expansion of the integer 8. The series identity is rigorous; the required tail lower bound remains unproved. If a gate fails, the actual machine must be followed through the separate signed negative macro, so the relaxed series alone does not decide later behavior.


## Generalized Lüroth form and relevant literature

Rescale once more by \(x=u/10\). The limiting map becomes
\[
L(x)=\frac{3^a x-1}{2}
\quad\text{on}\quad
3^{-a}<x\le3^{1-a},\qquad a\ge1.
\]
The branch lengths are \(2/3^a\), summing to one, and every branch maps onto \((0,1]\). This is a generalized Lüroth-type expansion with a geometric countable partition. The exact finite-band system is the non-autonomous perturbation
\[
x_{k+1}=\frac{3^{a_k}}2x_k-\frac12+\frac{3}{10\cdot2^{k+1}},
\]
with branch endpoints shifted by \(2^{1-k}/10\). The gate target is \(0<x_{k+1}<(k+7)/(10\cdot2^{k+1})\).

Relevant existing frameworks to consult before attempting a metric theorem:

- J. L. Fernández, M. V. Melián, and D. Pestana, “Expanding maps, shrinking targets and hitting times,” *Nonlinearity* 25 (2012), 2443–2471, [DOI 10.1088/0951-7715/25/9/2443](https://doi.org/10.1088/0951-7715/25/9/2443). Its stated scope includes uniformly expanding transformations and countable partitions, with Borel--Cantelli results for shrinking targets.
- Bo Tan and Qinglong Zhou, “Approximation properties of Lüroth expansions,” *Discrete and Continuous Dynamical Systems—Series A* 41 (2021), 2873–2890, [DOI 10.3934/dcds.2020389](https://doi.org/10.3934/dcds.2020389). This studies Diophantine approximation associated with Lüroth expansions.

These are methodological precedents, not plug-in proofs for #754: the distinguished seed is a specific rational point, the target is nonstationary and exponentially shrinking, and the exact map has band-dependent corrections. Any application must verify the hypotheses for this precise map and must still address the point \(x_0=4/5\), not merely almost every point.


## Exact non-autonomous Borel--Cantelli bound for the relaxed orbit

The exact finite-band maps admit a direct transfer-operator estimate; no shadowing by the limiting map is needed for this *metric* statement. Put
\[
c_k=10-2^{1-k},\qquad X_k=(0,c_k/10].
\]
For exponent \(a\ge1\), the exact branch domain is
\[
I_{k,a}=\left(\frac{c_k}{10\cdot3^a},\frac{c_k}{10\cdot3^{a-1}}\right],
\]
and the normalized relaxed map is
\[
F_{k,a}(x)=\frac{3^a}{2}x-\frac12+\frac{3}{10\cdot2^{k+1}}.
\]
The intervals \(I_{k,a}\) partition \(X_k\). Every branch maps onto the same interval
\[
Y_k=\left(\frac{1}{10\cdot2^{k+1}},\ 1-\frac{3}{10\cdot2^{k+1}}\right]\subset X_{k+1},
\]
whose length equals \(|X_k|=c_k/10\). The inverse-branch derivative is \(2/3^a\), independent of \(k\), and
\[
\sum_{a=1}^{\infty}\frac{2}{3^a}=1.
\]

Let \(f_k\) be the density of the pushforward of Lebesgue measure on \(X_0\) under the first \(k\) relaxed maps. The transfer operator is
\[
(\mathcal P_k f)(y)=\mathbf 1_{Y_k}(y)\sum_{a=1}^{\infty}\frac{2}{3^a}f(F_{k,a}^{-1}(y)).
\]
Therefore \(0\le f\le1\) implies \(0\le\mathcal P_k f\le1\). Since \(f_0=\mathbf1_{X_0}\), induction gives \(0\le f_k\le1\) for every \(k\). This is an exact L-infinity contraction for the non-autonomous relaxed system.

The positive-gate failure at band \(k\) is the target
\[
J_k=\left(0,\frac{k+6}{10\cdot2^k}\right)\subset X_k.
\]
Consequently
\[
\lambda\{x_0\in X_0:F_{k-1}\circ\cdots\circ F_0(x_0)\in J_k\}
=\int_{J_k}f_k(y)\,dy
\le\frac{k+6}{10\cdot2^k}.
\]
Summing and applying the first Borel--Cantelli lemma proves:

**Theorem (generic finite gate failures).** For Lebesgue-almost every initial \(x_0\in X_0\), the relaxed exact positive-return orbit has only finitely many indices \(k\) with \(q_k<k+6\). More quantitatively, for every \(N\ge0\),
\[
\lambda\{x_0\in X_0:\exists k\ge N,\ q_k<k+6\}
\le\sum_{k=N}^{\infty}\frac{k+6}{10\cdot2^k}
=\frac{N+7}{5\cdot2^N}.
\]
For the uniform probability measure on \(X_0\), divide this bound by \(|X_0|=4/5\), obtaining \((N+7)/(4\cdot2^N)\).

This is stronger than the limiting-map metric observation: it applies to the exact non-autonomous relaxed recurrence. It still does **not** decide the distinguished seed \(x_0=4/5\), a measure-zero endpoint of \(X_0\). Nor does it prove that the actual Turing-machine trajectory is nonhalting: after a first gate failure the machine follows the separate signed negative macro, whereas the theorem continues the relaxed positive recurrence. The theorem controls the measure of initial seeds whose relaxed orbit has late gate failures, not the actual negative-phase outcomes for #754.
