# Exact source-parent fan for the residual (y=3, x\equiv10\pmod{16}) family

**Status:** Independent exact derivation and side-condition audit of the multiple-depth parent fan already recorded in `M0EvenEvenSumZeroNextCandidates.md`. The same valuation formula and parent count are already present there; this note does not add a new residue cylinder or nonreachability result. Its incremental details are an explicit contiguous depth interval, the converse branch inequalities, a stronger `k_d≥5` bound, and an alternate proof that the exceptional `a=1` row is impossible. No Lean compilation was possible in this invocation because the local Python and container runtimes returned tool-level `ClientError`; no CI substitute was used.

## 1. The residual parameterization

The remaining (u=5, r\equiv1\pmod4) branch in `M0EvenEvenSumZeroNextCandidates.md` has
[
129+211s=5\cdot2^r,qquad s\equiv5\pmod8,qquad r\equiv1\pmod4,
]
and its terminal target is
[
(x,3),\qquad x=302+512s-4r.
]
The congruence (2^r\equiv68\pmod{211}), together with the order (210) of (2\pmod{211}), gives
[
r\equiv201\pmod{210}.
]
Intersecting with (r\equiv1\pmod4) yields
[
r=201+420\ell,\qquad m=(r-1)/4=50+105\ell.
]
Put
[
H=19+32s-m.
]
Then
[
x+6=16H,
\qquad
H=\frac{320\cdot2^{4m}-211m-119}{211}
 =\frac{5\cdot2^{4m+6}-A}{211},
\qquad A=211m+119=10669+22155\ell.
]
In particular (H\in\mathbb N), (H>0), and (x\equiv10\pmod{16}).

For (m\ge50), the elementary inequalities
[
0<A<2^{4m+6},\qquad 5\cdot2^{4m+6}>212A
]
hold. For completeness, (2^m\ge m^3) for (m\ge10) by induction, so (2^{4m+6}\ge64m^3); also (A<214m) and (320m^3>212\cdot214m) for (m\ge50). Thus the displayed inequalities follow. In particular (H>A), and because the two terms (5\cdot2^{4m+6}) and (A) have different 2-adic valuations,
[
\nu:=v_2(H)=v_2(A)=v_2(10669+22155\ell).
]
Consequently (2^\nu\le A<H), so **(H) is not a power of two**. This last fact eliminates the exceptional (a=1) source row below.

The valuation formula is useful in its own right: since (22155) is odd, for every (e\ge1) there is exactly one residue class of (\ell\pmod{2^e}) for which (\nu\ge e). Hence (\nu), and therefore the number of possible immediate parents, is unbounded over this one-parameter family. A fixed-depth parent search cannot be complete.

## 2. Complete parent classification

Let
[
D=\left\lfloor\frac{\nu+2}{2}\right\rfloor.
]
For each integer (d\) with (0\le d\le D), define
[
a_d+3=\frac{16H}{2^{2d+1}},
\qquad
2k_d=x+1-a_d-6d.
]
These are natural numbers, with (a_d\ge3) odd and (k_d\ge5). More explicitly,
[
(a_0,k_0)=(8H-3,\;4H-1),
]
[
(a_1,k_1)=(2H-3,\;7H-4),
]
and for (d\ge2),
[
(a_d,k_d)=
\left(
\frac{H}{2^{2d-3}}-3,
\;8H-\frac{H}{2^{2d-2}}-1-3d
\right).
]
All displayed divisions are exact for (d\le D).

**Theorem (exact finite source-parent fan).**
For the authentic Machine C section transition `secNext`,
[
\operatorname{secNext}(a,k)=\operatorname{some}(x,3)
\quad\Longleftrightarrow\quad
\exists d\le D,\ (a,k)=(a_d,k_d).
]
Equivalently, for genuine blank-origin section reachability,
[
\operatorname{CReach}(x,3)
\quad\Longleftrightarrow\quad
\exists d\le D,\ \operatorname{CReach}(a_d,k_d).
]

**Derivation from the exhaustive source grammar.**

- The (a=0) rows cannot output (y=3).
- The finite (a=1) row outputs ((2,3)), not this large (x). Its remaining (y=3) row requires (x+6=16\cdot2^n), equivalently (H=2^n), which is impossible because (H) is not a power of two.
- For (a\ge2), the direct/low rows output even (y), and the even-(a) bounce row requires (y\ge4).
- Therefore every remaining parent has odd (a\ge3) and lies in the odd-(a), (y=3) bounce row. The exact source equations there are
  [
  x+6=2^{n+1}(a+3),\
  2k+a+3n=x+1.
  ]
  Since (x+1) and (a) are odd, the second equation forces (n) even. Write (n=2d). Since (a+3) is even, the first equation forces
  [
  2d\le\nu+2,
  ]
  hence (d\le D), and solving the two equations gives exactly ((a_d,k_d)).
- Conversely, for every (d\le D), (a_d+3) is even and at least (6), and
  [
  2k_d-a_d
  = (2^{2d+1}-2)a_d+3\cdot2^{2d+1}-6d-5>0,
  ]
  Thus the branch condition `2*k_d > a_d` and the natural-subtraction side condition in the odd-(a), (y=3) source row both hold. Substitution verifies both source equations, so every listed pair really is a predecessor.
- The target is not the blank seed ((5,1)). Therefore a genuine visit to ((x,3)) has a positive-time predecessor, and each listed source edge also transports reachability forward by one step. This gives the stated reachability iff.

The exact parent count for a fixed ℓ is therefore
[
1+\left\lfloor\frac{v_2(10669+22155\ell)+2}{2}\right\rfloor,
]
which is finite for every ℓ but unbounded over the family.

## 3. What this does and does not settle

This does not close a new classification gap: the earlier `M0EvenEvenSumZeroNextCandidates.md` already records the same multiple even-depth fan, valuation, and parent count. This file independently derives the same family and makes the permitted depths exactly `0≤d≤D`, while checking the converse source-branch side conditions and strengthening the lower bound on the parent right coordinate to `k_d≥5`. The residual (u=5, r\equiv1\pmod4) reachability question remains open.

For (d\ge2), writing (R_d=H/2^{2d-3}) gives the convenient form
[
a_d=R_d-3,\qquad
k_d=8H-R_d/2-1-3d,\qquad
a_d+k_d=8H+R_d/2-4-3d.
]
This exposes the next task: combine the parity and 2-adic residues of (R_d), (k_d), and (a_d+k_d) with the already source-certified odd-image, odd/odd low-valuation, odd/odd sum-16, even/odd, and even-right inverse theorems. The cases where a parent sum is divisible by (16) (or by (32)) are precisely where the currently available low-valuation parent lemmas stop applying; those branches must not be silently discarded.

A useful next step is to derive a second-level parent fan for the (d=0,1) branches on the nested ℓ-residue classes where their sums have valuation at least four, then compare that fan with the higher-(d) parents. The formulas above make that comparison exact and avoid repeating any finite quotient search.
