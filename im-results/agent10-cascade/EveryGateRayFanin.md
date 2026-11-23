# Every sufficiently large surviving #746 gate has an inverse-ray state with arbitrarily large genuine fan-in

**Status (23 November 2026): new paper-level all-index theorem.** The arithmetic and its source-grammar composition are given below, and the exact BigInt witness construction is in [`every_gate_ray_fanin.mjs`](every_gate_ray_fanin.mjs). The modular selector and source-band composition in this note have **not** been compiled together in Lean. The existing source-level parent grammar and every-three-valuation parent theorems are independently Lean-accepted; that does not yet constitute formal acceptance of this new quantified theorem. This is a statement about **synthetic predecessors** of authentic original #746 fatal gate heights, **not** their reachability from the blank root and not a #746 or BB(6) decision.

## Uniform theorem

Write `p=2^n`, `c=2n+3`, `a=⌊log₂ c⌋`, `J=n−a`, and `u_j=4p+n−1−c·2^j`, the exact source-C inverse even ray from the fatal reset height `u_0=4p−n−4`. Let `ResetParent(h,u)` denote the **untruncated** genuine source-C first-reset parent relation in [FirstInverseComplete.lean](FirstInverseComplete.lean).

**Theorem (all surviving indices, unbounded ray fan-in).** For every integer `m≥1` and **every** integer `n≥100·3^(3m+1)` with `n mod 6 ∈ {4,5}`, there is an **even** index `j` satisfying
`0≤j<2·3^(3m)` and `j+8≤J`
such that `u_j` has **at least m+1 pairwise distinct genuine ResetParent predecessors**. One is the canonical even parent `u_(j+1)`. For each `b=0,…,m−1`, another parent comes from a valid *odd* valuation `t_b∈{3b,3b+1,3b+2}`. In particular, the maximal immediate inverse fan-in somewhere on the canonical ray grows at least on the order of `log n`, **uniformly over both surviving gate sectors**, not just on a sparse subsequence of gate indices.

The conservative constant 100 makes all tape-band and ray-length estimates immediate; it is not sharp. This strengthens the forced `t=3` theorem in [GateTargetSpineEmbedding.md §12](GateTargetSpineEmbedding.md#12-universal-forced-t3-triple-branch-in-every-surviving-gates-first-54-ray-states), which guaranteed three parents at a ray position for each gate, to **any prescribed number** of actual distinct parents for all sufficiently large gates. Unlike Agent44's [source-certified unbounded fan-in at the fatal height itself](../agent44-746-fanin/README.md), this theorem selects a possibly nonzero ray depth `j(n,m)` and works for **every** sufficiently large surviving `n`. It uses Agent44's already proved exact odd-inverse machinery rather than reconstructing it.

## Proof

**1. Unique even ray index of arbitrary prescribed 3-adic precision.** Put `T=3m+1` and `A=8p+2n+3`. At every surviving `n` we have `3∤2c` and `A≡2c (mod 3)`. For `n≡4 (mod 6)`, both residues are 1; for `n≡5 (mod 6)`, both are 2.

The element `4` generates the group of units congruent to 1 modulo 3 in `(ℤ/3^Tℤ)×`. Indeed `v₃(4^(3^s)−1)=s+1`: the initial value is `v₃(4−1)=1`, and cubing a number `1+3^r z` with `3∤z` increases that valuation by exactly one. Thus the order of `4` modulo `3^T` is `3^(T−1)`, the size of that unit subgroup. Hence there is a unique `r∈{0,…,3^(T−1)−1}` with
`2c·4^r≡A (mod 3^T)`.
Take `j=2r`. By the exact ray formula,
`X_j:=2u_j+5=A−2c·2^j`
is a positive odd multiple of `3^T`. Notice that this selector works **for every eligible n**; no Hensel-compatible subsequence restriction on n is needed.

**2. The selected vertex is a genuine interior ray vertex.** Since `n≥100·3^T`, `j<2·3^(T−1)≤n/150`. The elementary inequality `2n+3<2^⌊n/2⌋` for `n≥10` (base cases 10 and 11, then induction in steps of 2) gives `a<n/2` and hence `J>n/2`. Therefore `j+8≤J`. From `2^a≤c<2^(a+1)` we get `c2^J<2p`; consequently
`2c2^j≤2c2^(J−8)<p/64`.
Also `2n+3<p`; hence
`7p<X_j<9p`.
For the original even arm at scale `k=n−1`, `u_j` lies strictly in the band `3p−1≤u_j≤4p−3`, and direct substitution gives `2u_j=8·2^(n−1)+u_(j+1)+(n−1)`. Thus `ResetParent(u_(j+1),u_j)`; moreover `u_(j+1)>3p`.

**3. Every three adjacent valuations contribute an authentic odd parent.** Since `3^(3m+1)|X_j`, for every `b<m` the [kernel-checked source-linked theorem `CascadeAgent44.every_three_odd_params`](../agent44-746-fanin/OddGroup.lean) produces an exponent `3b≤t_b≤3b+2` and an `OddParam(u_j,t_b)` witness. [`odd_param_exact_parent`](../agent44-746-fanin/ExactOdd.lean) turns it into an actual `OddParentAt(u_j,h_b,t_b)` witness and hence `ResetParent(h_b,u_j)`.

For intuition, if `X_j=3^(3b+4)e` with odd `e`, the three possible odd source parameters are `27v,18v,12v`, where `v=2^(3b)e`. Agent44's exact dyadic triple-band lemma proves one is in a strict valid source band, with the corresponding valuation in `{3b,3b+1,3b+2}`. No assumption `3∤e` or truncation to a maximal t is made. (Using a source gap for *only* the maximal allowed valuation would be invalid.)

**4. The parents really are distinct.** The blocks of valuation exponents are disjoint, so [`odd_parent_valuation_unique`](../agent44-746-fanin/ExactOdd.lean) makes the `m` odd parents pairwise distinct. The valuation `t=0` cannot be source-valid here: `X_j/3∈(2p,3p)`, a strict gap between the bands at scales `n−2` and `n−1`. Hence every selected odd `t_b≥1`, and its source parameter `2^t X_j/3^(t+1)<2p`; its band level must be `k≤n−2`, so its source parent satisfies `h_b<8·2^k≤2p`. The canonical even parent exceeds `3p`, hence differs from all of them. We have `m+1` distinct genuine parents, as claimed.

**Explicit growth corollary.** For every surviving `n≥8100`, every integer `m≥1` satisfying `100·3^(3m+1)≤n` is a lower bound (minus one) on the maximum immediate fan-in on that gate's canonical inverse ray. Therefore this maximum is `Ω(log n)`, uniform in `n≡4,5 (mod6)`.

## Reproduction and falsifiers

The linked dependency-free Node BigInt script computes the **unique modular index by successive ternary Hensel digits**, constructs the huge literal `u_j`, and checks all even/odd source bands and algebraic parent identities using integers, with no floating-point geometry. It checks witness injectivity and one valid odd exponent in each required disjoint three-block. Representative runs:

| n | m | T | selected j | accepted odd valuation t values | guaranteed block coverage |
| ---: | ---: | ---: | ---: | --- | --- |
| 8200 | 1 | 4 | 28 | 1, 3 | {1} |
| 220000 | 2 | 7 | 834 | 1, 3, 6 | {1}, {3} |
| 1000000 | 3 | 10 | 25000 | 1, 3, 6, 8 | {1}, {3}, {6,8} |

The exact integer witnesses were evaluated independently in the functions JavaScript runtime; the saved Node file has not been executed in a local shell in this invocation because the shell endpoint returns `ClientError` before commands execute. A falsifier would be a surviving `n≥100·3^(3m+1)` for which no even `j<2·3^(3m)` has `3^(3m+1)|X_j`, an invalid source band at one of the selected three-blocks, or duplicate source heights for distinct valuations. The preceding group-order, band, and unique-valuation arguments rule out each possibility on paper.

## Scope and next proof edge

This is a **universal inverse-branching obstruction**, not evidence that any of those off-ray parents are blank-root reachable or that any fatal gate is accessible. The exact missing Lean source integration is the all-T modular-selection theorem (primitive-root/Hensel lifting), the elementary `j+8≤J` bound, and the canonical even-parent separation; Agent44's all-valuation parent and injectivity lemmas can be imported unchanged. A useful solver must now rule out rooted paths along these arbitrarily broad inverse fans using a truly global invariant, or exhibit a genuine root-to-fatal path. Another fixed-depth residue census will not establish the machine-wide decision.
