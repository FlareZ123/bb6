# P1 inverse shadow: an exact critical first-moment law

**Status, 9 November 2026:** exact all-generation first-moment and local offspring-distribution theorems for the source-derived **abstract two-counter P1 inverse shadow**, with self-contained cylinder/valuation proofs, independent exact-integer regressions, and Lean-checked universal arithmetic lemmas. Original-source Lean integration of the *statistical theorem* has not been completed; external novelty has not been assessed. Neither the original P1 machine nor BB(6) is decided.

## The precise model and theorem

Fix an integer parameter `q ≥ 0` and one of the two genuine P1 feeder labels `s ∈ {8,9}`. The source-derived shadow inverse grammar is the one in [Agent 9's P1 shadow analysis](../agent9-p1-shadow/README.md), also used by [Agent 13's generic finite checker](../agent13-p1-adaptive-param/README.md):

- `s=8`: initial state `(m,z)=(0,12q+4)`;
- `s=9`: initial state `(m,z)=(0,10q+4)`;
- a depth `t ≥ 0` is admissible at `(m,z)` exactly when `2^t | z` and `16q+s+m+t+z/2^t` is odd;
- its child is `(m+t+1,(16q+s+m+t+z/2^t-1)/2)`.

Count **depth words, with multiplicity**. Two words reaching the same pair remain distinct; this convention is essential. Write `N(s,d,T;q)` for the number of legal words of length `d` when *every* constituent depth is at most `T`.

**Exact finite binary-cylinder theorem.** For every `d≥1,T≥2`, and every `K≥d(T+1)-2` when `s=8`, respectively `K≥d(T+1)-1` when `s=9`, the following identities hold exactly (not asymptotically):

```text
(1/2^K) ∑_{q=0}^{2^K-1} N(8,d,T;q)
  = (2 - 2^(1-T)) (1 - 2^(-T-1))^(d-1),

(1/2^K) ∑_{q=0}^{2^K-1} N(9,d,T;q)
  = (2 - 2^(-T)) (1 - 2^(-T-1))^(d-1).
```

The same equalities hold over **any** block of `2^K` consecutive nonnegative integers, since every accepted word is a single congruence cylinder of modulus dividing `2^K`. In particular they hold on arbitrarily high blocks `q≫29`, which is the domain where the source reductions are used.

**Unrestricted inverse depth: exact Haar first moment.** Let `N(s,d;q)` count all legal length-`d` words with no bound on their depths, and let `q` be Haar-uniform in the 2-adic integers. Then, as an identity of nonnegative extended random variables,

```text
E_Haar[N(8,d;q)] = E_Haar[N(9,d;q)] = 2
for every d≥1.
```

This is a first-moment statement. It does **not** say that these paths are independent, or that a positive-measure set of parameters admits infinite inverse histories.

**A rigorous obstruction to uniform bounded inverse searches.** Let `F_s(q)` denote the total count of finite legal shadow inverse words of *all* lengths (including the empty word), allowing `+∞`. Then

```text
lim_(Q→∞) (1/Q) ∑_{q=0}^{Q-1} F_s(q) = +∞
for s=8 and s=9.
```

Indeed for each fixed `D,T`, `F_s(q)≥1+∑_{d=1}^D N(s,d,T;q)`; average the finite periodic summands, then let `T→∞` and finally `D→∞`. For arbitrarily large `D`, there are entire nonempty high-parameter binary cylinders supporting genuine shadow paths of depth at least `D`. Thus no parameter-independent finite bound on the number of *shadow inverse words* can be valid.

This average divergence does not establish the existence of a single infinite path for a given ordinary integer `q`, let alone a P1 halt. It does show precisely why uniformly finite-depth exhaustive inverse-graph arguments cannot cover all parameters.

## Exact offspring distributions and criticality

For a fixed odd-slope parameter cylinder `q=q₀+2^h r`, the second coordinate `z=a+b*r` has odd `b`. Under Haar-uniform `r`, its 2-adic valuation `V=v₂(z)` has `P(V=v)=2^(-v-1)`, independently of `a,b`. Let `C=(s+m) mod 2` and let `B` be the number of all **unbounded-depth** legal children of this one abstract node. At the two root feeders, use `B_root`.

| Location | Exact offspring law | Mean | Variance |
| --- | --- | ---: | ---: |
| Either feeder root | `P(B_root=1)=1/4`; `P(B_root=r)=9/4^r` for `r≥2` | 2 | 2/3 |
| Generic odd-slope node, `C=0` | `P(B=0)=1/4`; `P(B=r)=9/4^(r+1)` for `r≥1` | 1 | 2/3 |
| Generic odd-slope node, `C=1` | `P(B=0)=1/2`, `P(B=1)=1/8`; `P(B=r)=9/(2*4^r)` for `r≥2` | 1 | 4/3 |

The exact second moments are respectively `14/3`, `5/3`, and `7/3`. The root law is a one-unit shift of the `C=0` generic law, despite the two feeder roots having distinct formulas.

**Derivation.** For `z>0` with valuation `v`, the quotient `z/2^t` is even for all `0≤t<v` and odd at `t=v`. Therefore every lower depth is legal precisely when `C+t` is odd; the endpoint depth `t=v` is legal precisely when `C+v` is even. Thus, writing `v=2k` or `v=2k+1`, the generic child counts are

```text
C=0:  B(2k)=k+1, B(2k+1)=k
C=1:  B(2k)=k,   B(2k+1)=k+2.
```

At `s=8`, the root count is `k+2` or `k+1` according as `v₂(3q+1)=2k` or `2k+1`. At `s=9`, the same rule holds with `v₂(5q+2)`. The odd coefficients 3 and 5 ensure each valuation is geometrically distributed. Grouping adjacent even/odd valuations yields the table. Summing the elementary series `∑r x^r=x/(1-x)^2` and `∑r² x^r=x(1+x)/(1-x)^3` at `x=1/4` gives the rational moments without simulation or probabilistic independence assumptions.

**Interpretation:** every non-root cylinder has mean **one** child. This is a first-moment critical branching law, with two different parity-conditioned variances. Actual sibling nodes have overlapping parameter cylinders; their future offspring are correlated. The law alone gives no extinction theorem and cannot be substituted for a Galton–Watson model. A finite set of residues may carry many overlapping depth words even though the averaged generation width remains constant.

## Proof: exact binary-cylinder conservation

A symbolic parameter cylinder of mass `2^-h` can be written as `q=q₀+2^h r` with `r` unrestricted and a current affine second coordinate `z=a+b r`, where **b is odd** and `m` is fixed along the word.

For a proposed depth `t`, divisibility and odd-next-coordinate are exactly the single congruence

```text
a+b*r ≡ δ * 2^t  (mod 2^(t+1)),
δ = 1 - ((s+m+t) mod 2).
```

The term `16q` is even and hence does not change this parity. Since `b` is odd, multiplication by `b` permutes residues modulo `2^(t+1)`. **Exactly one** residue of `r` modulo `2^(t+1)` is legal. Its child cylinder has relative mass `2^(-t-1)`. If that residue is `r₀` and `r=r₀+2^(t+1)u`, the child second coordinate is again affine in `u`, with new slope

```text
b' = b + 16*2^h*2^t,
```

which is odd. The mass of all children with `0≤t≤T` is therefore exactly

```text
∑_{t=0}^T 2^(-t-1) = 1 - 2^(-T-1)
```

times the mass of their parent, **for every odd-slope cylinder**, without independence assumptions. The same calculation applies independently to every word, so summing with multiplicity preserves this factor at each subsequent generation.

It remains to initialize the two genuine feeder forms, whose starting slopes are even.

For `s=8`, `z=4(3q+1)`. Of the depths below two, only `t=1` is legal, **for every q**; it has child `z'=11q+5` with odd slope. For each `t≥2`, precisely one residue of `q modulo 2^(t-1)` is legal; it has mass `2^(-(t-1))` and child odd slope `3+8*2^(t-1)`. Hence the first-generation truncated mass is `1+∑_{t=2}^T 2^(-(t-1))=2-2^(1-T)`.

For `s=9`, `z=2(5q+2)`. Depth `t=0` is legal for every `q`, producing `z'=13q+6`. Each `t≥1` selects one residue modulo `2^t`, of mass `2^-t`, with odd child slope `5+8*2^t`. The first mass is `2-2^-T`.

By induction on word length, every subsequent generation multiplies that total mass by `1-2^(-T-1)`. A first feeder edge consumes at most `T-1` or `T` parameter bits respectively, and every later edge consumes at most `T+1`. Consequently every word's cylinder modulus divides `2^(d(T+1)-2)` or `2^(d(T+1)-1)` respectively, proving the finite averaging formulas and block-periodicity.

As `T→∞`, the bounded-word random variables increase monotonically to unrestricted `N(s,d;q)`. Their Haar expectations tend to `2`, and monotone convergence proves the exact first moment. For ordinary integer parameters, each fixed finite cutoff statistic is periodic; taking its exact Cesàro average gives the divergent-mean corollary as stated.

## Reproduction, verification and precise scope

- [`finite_cylinder_regression.py`](finite_cylinder_regression.py) independently builds exact symbolic congruence cylinders with `Fraction` weights and directly enumerates every integer `q` in complete dyadic periods. It verifies `T=2,3,4`, levels `d=1,2,3,4` in the symbolic check and both feeders with `T=3,d≤3,K=13` in the direct check. These are **tests** of the complete all-`d,T` proof above, not a replacement for it.
- [`offspring_law.py`](offspring_law.py) checks both root counts and both generic parity laws directly for every `q mod 8192`, verifies the exact geometric valuation masses, and checks first/second moments against their exact rational limits. The local run passed all assertions; the paper proof is the complete all-depth argument.
- [`P1DyadicWidthCore.lean`](P1DyadicWidthCore.lean) is a locally checked, standalone Lean **arithmetic bridge**, not a kernel proof of the entire count. In Lean 4.36.0-rc2, `odd_slope_step`, `odd_root_slope`, `bit_flip`, `scaled_div`, and `child_affine` all compile with no `sorry`. Printed axioms are contained in `[propext, Quot.sound]`. `bit_flip` certifies the parity-bit flip on advancing a parameter by one modulus; `child_affine` certifies the exact affine slope transport without rational arithmetic.
- The shadow recurrence is already established as source-derived by the cited Agent 9 and Agent 13 work. This theorem is **about legal abstract inverse words**, not every original raw-machine transition. A uniform source-connected theorem lifting all bounded words at sufficiently high `q` has **not** been proved here. Do not claim that the unbounded abstract average transfers to actual blank-reachable machine states.
- Originality relative to external literature and priority over prior P1 shadow investigations remain to be independently reviewed. This is therefore maintained in `im-results/` rather than `results/`.

**Next decisive mathematical question:** quantify **generation-level** second moments and survival probabilities of the correlated inverse-cylinder tree, and prove a source-connected, uniform-in-`q` lift for bounded-depth words. The local second moments above are for a *single node*, not for the generation total. A proof that the survival probability tends to zero would be a much stronger **density-one** statement but would still require handling genuine non-odd exits before becoming a P1 halting decision.
