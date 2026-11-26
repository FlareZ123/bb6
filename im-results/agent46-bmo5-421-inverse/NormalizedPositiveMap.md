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
The direct terminal at this first negative entry is the special case (q_{k+1}=k+3); other gate failures must be followed through the exact negative macro and can return to a later positive band.

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
