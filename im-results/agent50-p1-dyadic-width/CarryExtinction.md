# Density-zero unrestricted critical P1 right-five gate

**New result, 2026-11-24 (Agent50).** Let E be the set of ordinary integers n >= 14 for which there exist b,m with the ORIGINAL source relation
`OddCone (14*2^n-2*n-16) 3 b 5 m`.
Then E has natural density zero. This includes arbitrary inverse depth and cost, not only a selected restart family or bounded-shallow subcone. The same relative density-zero conclusion holds along every fixed infinite arithmetic progression. No assertion that E is empty, and no conclusion of BB(6) or unconditional P1 nonhalting.

## Finite theorem and proof

Write W_K(n) for the number of length-K Boolean words with x_0=1 and
```
sum_{j=0}^{K-1} x_j (n+j+3) 2^j = 1 mod 2^K.
```
Count words with multiplicity. In particular W_1(n) is 1 for even n and 0 otherwise. W_K is periodic modulo 2^K. For each valid prefix and each of its two extensions, exactly one of the two parameter lifts n and n+2^K satisfies the next congruence: the coefficient of the parameter is the odd number sum x_j 2^j. Consequently
```
W_{K+1}(n)+W_{K+1}(n+2^K)=2 W_K(n).
```
The mean width at each dyadic level is 1/2, and zero width persists on all descendant cylinders. This is an exact conservation law, not an assumption of independent branches.

Let r_0=1, r_{i+1}=r_i+2^{r_i}; the initial values are 1,3,11,2059. For any n and k, choose K>r_k, K<=r_{k+1}+1 with n+K+3 congruent to r_k modulo 2^{r_k}. For example K=r_k+1+2^{r_k}-(n+4 mod 2^{r_k}). Since r_k congruent to r_i modulo 2^{r_i} for each i<=k, the coefficients at all positions j_i=K-r_i vanish modulo 2^K. These are distinct nonleading positions. They may be toggled freely and independently in each valid word; hence 2^{k+1} divides W_K(n).

If a residue survives to level M>=r_{k+1}+1, it has positive width at the above checkpoint and thus width at least B=2^{k+1}. The dyadic first-hit cylinders at threshold B are disjoint. Each cylinder at level j has total width among its level-M descendants equal to 2^{M-j} W_j, by repeated conservation. This pays for at least B per descendant, even if the descendant eventually dies. The total width budget at level M is 2^{M-1}. It follows that
```
2^{k+1} * #{0<=a<2^M : W_M(a)>0} <= 2^{M-1}.
```
This proves that infinite carry survival has Haar measure zero in the 2-adic integers. It also proves any single infinitely surviving parameter must have unbounded width; the argument is entirely deterministic before taking density.

## Exact source bridge

The earlier P1CarryExact and P1CarryExactSource modules prove every valid word of cost K<=n produces an original OddCone history of cost K. P1CarryExactReverse now proves the converse for all original histories of cost m>=K, including m>n: split the source gaps into Micro steps and restrict to cost K. The exact identity, with v=(d-1)/2, T=7*2^n, is
```
2^m v + sum x_j(n+j+3)2^j = 1 + T sum x_j 2^j.
```
Thus for n>=14 and 0<K<=n, W_K(n)>0 iff some original history has total cost >=K. If W_K=0, every original history has cost <K. At positive cost <=n its shifted right coordinate v>=7 by the previous size bounds; at cost zero d=3. Hence no original history can end at d=5.

For any fixed M>=r_{k+1}+1 and ordinary n>=M, membership in E implies W_M(n)>0. The finite bound and periodicity therefore give upper natural density of E <= 2^{-(k+2)}. As k is arbitrary, the density is zero. Restriction to a fixed progression a+bh, b>0, preserves relative density zero, by dividing the upper counting bound by the progression's positive density 1/b. This includes n=16q+2 and n=16q+14 and both local restart progressions. This strengthens earlier sparsity results restricted to bounded shallow words.

## Formal status and reproduction

Lean 4.36.0-rc2 compiled P1CarryExtinction.lean and P1CarryExactReverse.lean against the original seven-module source closure and the preceding exact-prefix modules (see CarryPrefixExact.md). Key checked theorems: width_conservation, free_checkpoint, live_budget, survival_bound, infinite_survival_unbounded, source_width_iff, source_width_zero_no_right_five, source_right_five_width_pos. The finite counting estimate and pointwise source implication are kernel checked; the limiting natural/Haar density corollaries above are elementary paper deductions. The list leaves enumerates residues in binary tree order; membership and length are checked, and distinctness follows by induction from the disjoint even/odd choices of the next bit. All displayed key theorem axiom reports contain only standard Lean axioms, no sorryAx. No computational sample is used.

## Remaining obstacle

The bound's horizons grow as iterated exponentials; this is a structural proof, not a practical finite cutoff. Density zero does not decide any exceptional ordinary parameter. The decisive remaining problem is pointwise exclusion or explicit resolution of those exceptional critical roots, then the other original machine gates.
