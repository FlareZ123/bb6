# Exact two-sided signed #429 windows for *every odd* near-power exponent

**Main theorem (fully explicit, elementary proof).** The original q0 signed radix-16 macro graph supports a strictly interior **two-sided window of radius m** about the **exact power-of-four rank** \(p=4^{2m+3}\), for **every integer m≥0**. Unlike the earlier [Cantor](LongTwoSidedMinimal.md) and [uniform reset](LongTwoSidedCantor.md) constructions, this is a dense all-odd-exponent family with a **three-block chronological macro word**. It uses no numerical search, limit argument, random statistics, or parameter-dependent Cantor congruences. It is a synthetic strict signed-graph phenomenon; **none of these configurations is asserted to be reached by the actual blank #429 machine.**

## The exact path

Fix any integer \(m\ge0\), let \(k=2m+3\) (odd), \(T=4^k=64\cdot16^m\), \(V=16^m=4^{k-3}\). The original q0 signed macro digits have increments and numerators
\[
\begin{array}{c|c|c}
d & p'-p & 16y'\\\hline
0&3&y\\
4&4&y+4p+18
\end{array}
\]
(these are **unchanged** source definitions, not an approximate or relaxed model).

There is an exact chronological macro path
\[
\boxed{0^m\quad4\quad0\quad0^m}
\]
with states
\[
\boxed{
(T-3m-7,\ 10V)\ 
 \xrightarrow{\;0^m\;}\ (T-7,\ 10)\
 \xrightarrow{\;4\;}\ (T-3,\ T/4)\
 \xrightarrow{\;0\;}\ (T,\ V)\
 \xrightarrow{\;0^m\;}\ (T+3m,\ 1).
}
\]
Every transition satisfies the integer divisibility guard exactly. In the middle,
\[
10+4(T-7)+18=4T,
\]
so the digit-four transition has next height \(T/4\); the following zero divides that by 16 to \(T/64=V\). The powers-of-sixteen zero runs are exact by construction.

The center \((T,V)=(4^k,4^{k-3})\) is an exact near-power signed q0 macro rank (coefficient a=2 and residue b=0 in the doubled rank \(P=2T=2\cdot4^k\)). The backward half of the path has m+2 source macro steps; the forward half has m. Thus the source-signed graph admits a **symmetric two-sided macro window radius**
\[
 \boxed{m=\frac{k-3}{2}}
\]
at *every odd k≥3*, and hence a symmetric halfstep radius \(2m=k-3\). In particular, this gives the sharp asymptotic obstruction
\[
 \boxed{\limsup_{k\to\infty}\max_Y
 \frac{\text{symmetric strict macro window radius at signed near-power rank }4^k}{k}\ge\frac12}
\]
(and the normalized halfstep radius bound is ≥1). It does not exclude a **larger** linear cutoff Ck and is far smaller than the proposed exponentially large wide radius.

## Strict positive cone at every intermediate macro state

The signed model's interior is \(p>0,\ y>0,\ 3y<p\). At the leftmost state
\[
3y=30V,\qquad p=64V-3m-7.
\]
The strict cone inequality is \(34\cdot16^m>3m+7\), true at m=0 (34>7) and preserved by increasing m (left side multiplies by 16, right side grows by 3). In the first m zeros, the height **decreases** and rank **increases**, so the left endpoint is the worst cone case for the entire zero block.

At \((T-7,10)\), \(30<T-7\) for T≥64. After the 4 digit, \((T-3,T/4)\) is strict because \(3T/4<T-3\) whenever \(T>12\). The next zero reaches center \((T,V)=(T,T/64)\), clearly strict; the final m zeros again strictly decrease height and increase rank, so all intermediate states remain strict. Every macro height is a positive integer by the explicit transitions. No source-specific **even-height A-phase lattice** condition is being omitted: these are already the actual paired source q0 radix-16 macros, not arbitrary halfstep branches.

## Finite witnesses, tests, and significance

The formula produces exact windows at **every** odd k≥3; for example:

| m | k=2m+3 | backward macro steps | forward macro steps | center state |
| ---: | ---: | ---: | ---: | --- |
| 1 | 5 | 3 | 1 | \((4^5,16)\) |
| 5 | 13 | 7 | 5 | \((4^{13},16^5)\) |
| 50 | 103 | 52 | 50 | \((4^{103},16^{50})\) |
| 340 | 683 | 342 | 340 | \((4^{683},16^{340})\) |

The explicit computation was replayed with arbitrary-precision signed BigInt for m=0,1,2,5,15,340, checking every original-source radix-16 division, strict cone, rank and final endpoint. A compact parameterized Lean source theorem would require only algebraic lemmas about powers of 16 and the source Path constructor. A finite pinned Lean witness at m=340 can be checked without unrolling an astronomical number of nonzero digits: only **one digit 4** appears, with two zero blocks.

**Research implications.** Source-level universal near-power no-crossing claims at macro radius \(ck\) for c<1/2 are false already on this simple all-odd-exponent family; no need for the more elaborate Cantor constructions to refute them. Those constructions still matter for the **long backward** histories (coefficient 19/5 versus k) and the distinct b=2,4 parametrizations. The outstanding #429 project needs a valid obstruction at the enormous radius \(\asymp 4^k/k\), possibly using authentic blank-root restrictions, and this theorem does **not** give a BB(6) solution.
