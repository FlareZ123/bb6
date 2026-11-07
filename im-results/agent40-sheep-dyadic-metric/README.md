# Exact directed metric of Sheep's generic dyadic quotient

**Agent 40, 7 November 2026. Intermediate mathematical result.** For every `p>=1`, the complete **all-pairs shortest-distance function** in the generic synthetic Sheep first-even quotient `G_p` modulo `2^p` has an exact inverse-word formula. Every exactly-k reachable set up to canonical code length is a single dyadic cylinder, and **every endpoint in that cylinder is realized by k consecutive genuine generic returns along one freely chosen positive-integer trajectory**; the directed eccentricities have a closed binomial distribution. This refines the prior shortest-to-zero and diameter theorems. It is a theorem about **independently witnessed synthetic quotient edges** and gives no actual blank-origin Sheep or BB(6) decision. Original-source Lean integration and external academic novelty review remain outstanding.

## Definition and prior certified ingredients

For a positive *generic* even Sheep section source `x=2^a u`, `a>=1`, odd `u>=5`, the published first section step is `F(x)=x+a+(u-1)/2`. If `F(x)-1=2^h v`, with odd `v>=5`, the first-even return is `E(x)=1+3^h v`. `G_p` has the even residues modulo `2^p` as vertices; `r->s` when there exists **some** legal positive generic x witnessing `x=r`, `E(x)=s` modulo `2^p`. Different edges may use different physical representatives; exceptional `u=3` returns are excluded.

The [Agent22 all-p inverse-word theorem](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md) gives each even residue r a unique canonical word `W_p(r)=((a_1,h_1),...,(a_j,h_j))` with letter costs `c_i=a_i+h_i+1>=2`, total cost `C<=p`, empty word for zero. At precision `t`, its inverse letter is

```
T[t,a,h](s) = 2^a * (1+2^(a+1))^(-1) *
              (3-2*a + 2^(h+1)*3^(-h)*(s-1))  (mod 2^t),
 c=a+h+1<=t.
```

The inverse result has valuation a, depends only on `s mod 2^(t-c)`, and every such algebraic edge has arbitrarily large **legal generic** integer witnesses via CRT. The same source proves a genuine generic edge from residue zero to every even target. The [Agent40 shortest-to-zero theorem](../agent40-sheep-coherent-audit/DYADIC-DISTANCE.md) proves `d_p(r,0)=j`.

## Theorem 1: every exact-k endpoint set is one cylinder

For the source word `W=W_p(r)` of length j, let `C_k=sum_{i<=k} c_i` (`C_0=0`), `t_k=p-C_k`, and `v_k=Phi_{t_k}(W[k:])`, the residue represented by the remaining suffix word at precision `t_k`. Precision zero has one residue, zero. Thus `v_0=r` and `v_j=0`.

For **every** `0<=k<=j`, the set of vertices reachable from r by **exactly k generic quotient edges** is precisely

```
R_k(r) = {s even modulo 2^p : s == v_k (mod 2^t_k)}.    (1)
```

Its size is `2^C_k` if `t_k>=1`, and `2^(p-1)` if `t_k=0`.

**Proof.** We establish an exact one-edge image formula for any suffix word `V=(a,h)::V'` at intermediate precision `t`. Put `c=a+h+1<=t`, `v=Phi_t(V)`, `v'=Phi_{t-c}(V')`. For every even full-precision source `x==v mod2^t`, the valuation `a<t` is fixed. Any genuine generic edge `x->y` has an actual odd-block length `h_0`, whose truncated length `h*=min(h_0,t-a-1)` satisfies `x=T[t,a,h*](y)`. Uniqueness of canonical words at precision t forces `h*=h` and `y==v' mod2^(t-c)`. Conversely for **any even y** with that latter congruence, choose `x=T[p,a,h](y)`. Its reduction modulo `2^t` is exactly `v` by inverse-map compatibility and contraction. Agent22's CRT witness proves this x-to-y quotient edge genuinely exists. Therefore the outgoing-neighborhood of the **entire cylinder** `x==v mod2^t` is exactly the cylinder `y==v' mod2^(t-c)`. Induction from the singleton cylinder `R_0(r)={r}` proves (1). Counting even lifts gives the sizes. QED.

**Complete directed distance:** For any even residues r,s, define `K={0<=k<=j: s==v_k mod2^t_k}`. Then

```
d_p(r,s) = min(K) if K is nonempty; otherwise j+1.       (2)
```

By (1) these are all paths of lengths up to j; if K is empty, the canonical j-edge path from r to zero followed by the zero-hub edge reaches every s in j+1 steps. This gives an `O(j)` exact distance test from the decoded word, for **every ordered pair**, at every p.

## Theorem 2: exact coherent free-start cylinders and distances

Define a *coherent* exactly-k endpoint from residue r to mean there exists **one** positive even section integer `x≡r mod2^p`, whose first k actual consecutive **generic, nonhalting** Sheep first-even returns are defined and whose kth value is congruent to target s. Unlike the synthetic graph definition, successive transitions must belong to the same physical integer orbit. The start x is freely chosen, possibly very large, and is never assumed to equal the real blank-entry integer 10.

**Theorem.** For every p,r and every `0<=k<=j=length(W_p(r))`, the coherent free-start exactly-k endpoint set is **the same cylinder (1)**, with infinitely many, arbitrarily large genuine positive starts for each target. Consequently, using Agent22's prior coherent `j+1`-step zero-hub construction, the exact coherent free-start shortest distance for every ordered pair is **the same formula (2)**, and the entire eccentricity formula (3) and census (4) hold verbatim for coherent free-start distances.

**Constructive proof.** Every coherent orbit projects to a synthetic path, so (1) already gives the necessary congruence. For the converse, fix a target `s≡v_k mod2^(p-C_k)`, and construct a **higher-precision reverse lift** of the given prefix word. Put `P=p+C_k`, start with `z_k=s` at precision p, and for `i=k,k-1,...,1` define `z_(i-1)=T[P-C_(i-1),a_i,h_i](z_i)` modulo `2^(P-C_(i-1))`. At the final step `z_0` is determined modulo `2^P`. Repeated inverse-map contraction and the hypothesis on s imply `z_0≡r mod2^p`.

Take `x=z_0+2^P n` for sufficiently large natural n. A source `x_i` congruent to `z_i` at the stated precision has exact 2-adic valuation `a_(i+1)`. From the inverse gate, the identity `2(F(x_i)-1)=(1+2^(a+1))u+2a-3`, and the fact that each target `z_(i+1)` is even modulo at least `2^1`, the value `F(x_i)-1` has **exact** valuation `h_(i+1)`, and the genuine even-return successor is congruent to `z_(i+1)` modulo its target precision. Precision drops by exactly `c_(i+1)`; it never drops below p, so each exact valuation is forced. The positive affine slope of each generic branch lets n be chosen large enough to enforce all odd-cofactor guards `u,v>=5`. Induction therefore produces one legal actual k-return orbit from x to the required s.

More explicitly, let `A=product_{i=1}^k 3^(h_i)*(1+2^(a_i+1))`, which is odd. On the fixed prefix branch, raising the start by `2^P` raises the final kth value **exactly by `A*2^p`**. Thus every sufficiently large member of the arithmetic progression `z_0+2^P n` is a valid start, retaining the same k letters, final target residue, and strictly increasing physical section values.

The coherent distance lower bound is inherited from graph paths. The construction above realizes every k<=j admitted by (2). The previously established [coherent source theorem](../agent22-sheep-mixed-hub/COHERENT-ORBIT.md) supplies, from every source residue, a freely chosen real trajectory of **j+1** generic first-even returns to every otherwise missing target. Hence the coherent minimum cannot differ from (2). QED.

[verify_coherent.py](verify_coherent.py) checks the entire cylinder for each source and k>=1 at every precision p<=8 with **21,590 literal consecutive single-integer first-even trajectories**, checking every prescribed (a,h), generic positivity guards, final residue, and the exact arithmetic-progression slope `A*2^p`. This is a finite independent physical-integer regression, separate from the all-p proof and from any original raw-tape simulation.

## Theorem 3: exact eccentricity of every vertex

For `p>=2`, let `j=len(W_p(r))` and `C=cost(W_p(r))`. Then

```
ecc_p(r) = j      when C>=p-1,
           j+1    when C<=p-2.                             (3)
```

At `p=1`, the sole even vertex zero has eccentricity zero.

**Proof.** Formula (1) makes `R_j(r)` the multiples of `2^(p-C)`. If `C>=p-1`, this includes every even residue, so eccentricity at most j; the known `d_p(r,0)=j` proves equality.

If `C<=p-2`, choose target `s=-2 modulo 2^p`. Its canonical word at any intermediate precision `t>=2` is `(1,0)` repeated `floor(t/2)` times, at cost `2 floor(t/2)>=t-1`. This follows inductively from `T[t,1,0](-2)=-2 mod2^t` and uniqueness, until the residue becomes zero at precision 0 or 1. If s were reachable in some k<=j, cylinder formula (1) would force the word suffix of cost `C-C_k` to encode `-2` at precision `t_k=p-C_k>=2`. Its cost is at least `t_k-1`, implying `C>=p-1`, contradiction. So s requires j+1 edges by (2). QED.

## Corollary 4: entire eccentricity census

For `p>=2` and `1<=e<=floor(p/2)`,

```
# {r even mod2^p : ecc_p(r)=e} = 2*binomial(p-1,2e-1).   (4)
```

All other counts are zero. In particular, the radius is 1; there are **2(p-1)** center vertices. The diameter `floor(p/2)` is attained by **two sources** for even p and **2(p-1) sources** for odd p>=3. For p=1 radius and diameter are zero.

**Proof.** The canonical-word count for length j and total cost <=b is `binomial(b,2j)`. By (3), eccentricity e arises from length-e words costing p−1 or p, and length-(e−1) words costing at most p−2. Thus its cardinality is

`binomial(p,2e)-binomial(p-2,2e)+binomial(p-2,2e-2)=2 binomial(p-1,2e-1)`

by Pascal's identity; binomial out-of-range values are zero. Summing gives `2^(p-1)`, the entire graph. QED.

## Reproducible independent finite regression and limits

[verify_eccentricity.py](verify_eccentricity.py) enumerates all modular inverse edges and uses independent BFS from **every vertex** for every p from 1 to 11. It checks (2)'s distance-to-zero consequence, (3) for every source, the `-2` witness, and (4)'s complete histogram. It also compares **all exactly-k reachability sets** with the predicted cylinders for every source and k up to its code length at p<=9: 1,535 equalities, zero mismatches. For p=10, the 512-vertex histogram is `{1:18,2:168,3:252,4:72,5:2}`.

The exact coherent lift and all-p metric paper proofs depend on Agent22's all-p inverse-word uniqueness and CRT-realizability premises. The original Sheep machine's [authentic section bridge](../agent16-sheep-even-return/README.md) succeeded in pinned original-source [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), but the complete graph-metric theorem here has **no source-importing Lean proof**. The new metric is exact for both synthetic paths and **freely selected coherent single-integer trajectories**. Its constructed starts depend on the target and may be arbitrarily large. It gives no all-time restriction on the unique genuine blank even-section trajectory from the fixed entry 10. Prove a source-root invariant or an actual halting witness to resolve that open problem. No exact BB(6) bound follows.
