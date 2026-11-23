# Arbitrary-depth original-source M8 exclusion tower for every odd stopping index

**Research state (23 Nov 2026):** Lean 4.36.0-rc2 compiled the exact proof bodies under explicit signature-compatible assumptions for the separately developed original Machine C source theorems. Full source-chain compilation is running in [CI 45099456878](https://github.com/FlareZ123/bb6/actions/runs/45099456878). This is a conditional-source, intermediate finding until that run succeeds; it neither settles Machine C nonhalting nor BB(6).

## The tower

For every odd \(m\ge1\), every \(r\ge1\) and every \(t\ge0\), define

\[
B=2^{2m+2},\quad Q=(B-1)/3,\quad
S_r=\sum_{i=0}^{r-1}B^i,\quad X_r=B^r,\quad
R_r=3(Q-1)S_r+1=X_r-3S_r.
\]
Let \(T=15+16t\) for \(m\equiv1\pmod4\), and \(T=5+8t\) for \(m\equiv3\pmod4\). Put
\[
N=(Q-1)m+Q(T+1),\qquad
j=R_r(m+1)+X_rT+3(S_r-1),\qquad
k=3X_rN-2.
\]
Both expressions are nonnegative naturals. The exact second-family stopping equation holds:
\[
k+j+3m+5=B(j+3).
\]
In fact \(Q(j+3)=X_rN+m\), proving the equation by \(3Q+1=B\).

**Unbounded normalization depth.** The residual \(N\) is \(4\pmod{16}\) when \(m\equiv1\pmod4\), and \(2\pmod8\) when \(m\equiv3\pmod4\). Thus \(k+2=3v2^d\), with \(v\equiv2\pmod8\), at *exact* odd-normalizer depth
\[
d=\begin{cases}
r(2m+2)+1,&m\equiv1\pmod4,\\
r(2m+2),&m\equiv3\pmod4.
\end{cases}
\]
The index has \(j\equiv m+1\pmod4\), so \(j\) is even and \((j+m)\equiv3\pmod4\); moreover \(2d\equiv m+1\pmod4\). The established M8 affine-quotient exclusion therefore proves \(\neg\operatorname{CReach}(2j+3,k)\) for **every** such \(m,r,t\). These are forbidden *stopping inputs*, not halting witnesses.

At each fixed \(m,r\), the index \(j\) advances by \(16X_r\) (first case) or \(8X_r\) (second case) as \(t\) grows. Different heights \(r\) have different exact normalizer depths and thus disjoint right-coordinate families. Depths grow without bound for **each fixed odd** \(m\). Level \(r=1\) agrees exactly with the earlier [single-depth construction](M8OddDeep.md).

For example \(m=1,r=2,t=0\) gives \((j,k,d)=(4298,64510,9)\). It obeys \(64510+4298+8=16(4298+3)\) and has \(k+2=3\cdot42\cdot2^9\).

## Exact separation from the previous dyadic-tower filter

At all levels,
\[
j+3m+3+3m(S_r-1)=X_r(m+T+1).
\]
Since \(B\mid X_r\) and \(B\mid(S_r-1)\), necessarily \(B\mid(j+3m+3)\). Consequently for any \(n+4\le2m+2\),
\[
(j+3m+3)\bmod2^{n+4}=0,
\]
whereas the earlier Agent19 dyadic-tower test requires residue \(2^{n+2}\). This is proven for arbitrary \(m,r,t,n\), not just sampled configurations. The construction avoids that **specific** earlier exclusion; other stronger filters may overlap and are not ruled out.

## Stronger separation: the full pre-M8 Agent19 joint sieve

The earlier dyadic-residue separation is only one part of a stronger result. [M8TowerLegacyPass.lean](M8TowerLegacyPass.lean) proves
```lean
theorem tower_passes_all_legacy_high_sieves (m r t : Nat)
    (hm : m%2=1) (hr : 1≤r) :
    BB6.Agent19Joint.highAllowed (towerIndex m r t) m
```
for **all** odd m, positive heights r and t≥0. The source-body proof locally compiles with no `sorryAx` when the original Agent3 and Agent19 high predicates are replaced with their **exact copied definitions** (rather than opaque assumptions). The proof is therefore a direct syntactic arithmetic comparison with the entire earlier maintained high sieve. The original `JointAllRoot` dependency chain has not yet been compiled together with it.

The remaining cases simplify by parity: the new j is even and (j+m)%4=3. Agent3's five base restrictions, the rectangular m%32=5/j%32=12 exclusion, and all four Agent19 special restrictions are incompatible with those residues. The all-depth pair-residue restriction fails by `tower_prior_avoided`. Consequently, assuming the source modules are accepted, each tower family removes infinitely many high candidates that **all survived the previous Agent19 joint parameter criterion**.

## Formal results

- [M8OddTower.lean](M8OddTower.lean): `tower_stopping_algebra`, `tower_every_odd_unreachable`, `tower_odd_depth`. Main root theorem has no `sorryAx` in local source-body compilation against exact-signature assumptions.
- [M8OddTowerPrior.lean](M8OddTowerPrior.lean): pure `tower_prior_divisible`, `tower_prior_zero`, `tower_prior_avoided`; only standard Lean axioms.
- [M8OddTowerStructure.lean](M8OddTowerStructure.lean): `tower_level_one_index`, `tower_index_step`, `tower_depth_increases`, `tower_disjoint_levels`; only standard Lean axioms.
- [M8GenericHigh.lean](M8GenericHigh.lean): general all-depth Diophantine source-exclusion theorem for any compatible \((m,d,j,t)\) satisfying \(Q(j+3)=m+2^d(2+8t)\). This gives a reusable entry criterion independent of the tower formulas.

**Proof boundary:** These modules transitively use `M8FilteredResidual.lean` and the original `affineQuotientExcluded_sound` theorem. Local preflight replaced already-established source dependencies with signature-matching axioms, so its absence of `sorryAx` does not alone certify the original Machine C model. The new source-integrated workflow is the acceptance test. The construction does not decide the complete infinite stopping locus.
