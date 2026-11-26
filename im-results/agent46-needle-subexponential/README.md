# Subexponential Space Needle finite-target cutoff

**Status:** mathematical derivation using the previously established exact counter semantics and dyadic cylinder uniqueness. The counting argument is new within the examined repository; external novelty remains unverified. The global counting version and source-linked cutoff are now Lean-checked, including original-source CI [45735902584](https://github.com/FlareZ123/bb6/actions/runs/45735902584). No claim of blank nonhalting or BB(6) maximality.

## Band theorem

The shifted counter has the exact successful transition
`x=2^v(2q+3), y=x+v+3(q+1)` for natural q,v; a power of two is terminal. Each successful edge is strictly increasing and its gain is at least the odd part 2q+3.

Fix k, B=2^k, a threshold 0≤V≤k, and a positive integer l with l(V+1)≥k. Consider n consecutive successful transitions whose n+1 counters are all in [B,2B). Partition into floor(n/l) disjoint full blocks, dropping at most l−1 final edges. Write G=2^(k−V), A=2^V, so AG=B.

* A low block contains at least one source valuation v<V. Since its source x≥B and its gain is at least x/2^v≥G, its total gain is at least G. In a strictly increasing band segment, there are fewer than A such blocks: their disjoint gains sum to at most the total drift, which is less than B.
* All other blocks have a valuation word w of length l over {V,...,k}. The established theorem `NeedleWord.cylinder_unique` (in `im-results/agent46-needle-coherent-paths/NeedleWord.lean`) gives congruence of any two starts realizing the same word modulo 2^S, where S=sum(v+1). Here S≥l(V+1)≥k. Distinct band starts differ by a positive integer less than B, so each word occurs at most once among these blocks. There are at most (k−V+1)^l such words.

Consequently floor(n/l)< A+(k−V+1)^l and
```
n < l * (2^V + (k−V+1)^l).
```
This statement covers arbitrary successful segments, not merely prepared terminal-feeder families. No distribution hypothesis is used.

## Executable cutoff

For each k define
```python
from math import isqrt

def band_fuel(k):
    V = min(k, isqrt(k * ((k+1).bit_length())) + 1)
    l = max(1, (k + V) // (V + 1))
    return l * ((1 << V) + (k - V + 1)**l)

def target_fuel(T):
    assert T >= 3
    return sum(band_fuel(k) for k in range(T.bit_length()))
```
For any successful path with positive starting counter and end ≤T, assign each edge to the band of its source. In each visited band there is a consecutive within-band segment followed by at most one departing edge. The strict band inequality gives at most band_fuel(k) source edges in that band, even if the path departs it. Summing proves the total number of successful edges ≤target_fuel(T). Thus a forward scan from x=3 through at most target_fuel(T) successful edges, stopping on terminal or overshoot, decides reachability of the particular shifted target T. For unshifted target d use T=d+2. One may take the minimum with previously certified quadratic/cubic fuel for practical finite inputs.

For K=floor(log2 T), V=O(sqrt(k log(k+2))) and l log2(k−V+1)=O(sqrt(k log(k+2))). The sum over k≤K is
```
2^O(sqrt(K log(K+2))) = T^o(1).
```
In particular this improves the asymptotic high-level transition count of the earlier source-linked cubic cutoff, O((T log T)^(1/3)). This is a bound on number of exact counter transitions, not yet an end-to-end bit-complexity analysis or a uniform bound on terminal exponents.

## What remains

The alternative global counting argument below is formalized in Lean. The sharper per-band sum above remains a paper-level variant. The result decides every *fixed* target with a stronger uniform finite budget, but does not eliminate the unbounded existential over terminal targets T=2^K. No BB(6) maximality consequence is claimed.

## Certified global counting version

For a successful prefix of length n ending below 2^(K+1), choose positive l and natural V with l(V+1)≥K+1. Partition into full blocks of length l. Each low block contains an edge of valuation v<V. Its source x has k=log2(x), and its dyadic band is partitioned into cells of width 2^(k−V) (natural subtraction). The gain exceeds or equals the cell width, so distinct low blocks have distinct cell indices. There are at most (K+1)2^V possible indices. Every high block has a valuation word of length l over {0,...,K}, with sum of weights v+1 at least K+1. Equal words force starts congruent modulo 2^(K+1) by cylinder uniqueness, impossible for distinct strictly increasing starts below that bound. Separate low and high codes give

    n < l * ((K+1)*2^V + (K+1)^l + 1).

The executable Lean cutoff chooses K=log2(T), V=isqrt((K+1)*(log2(K+1)+1))+1 and l=(K+1+V)/(V+1). This yields the same subexponential asymptotic as above. See [NeedleSubexp.lean](NeedleSubexp.lean), locally checked with the standard axioms only, and [NeedleSubexpSource.lean](NeedleSubexpSource.lean), whose original-source reachability equivalence passed CI 45735902584. This is a uniform finite-target cutoff, not an all-exponent terminal exclusion or a proof that the blank trajectory survives.
