# P1 inverse shadow: an exact critical first-moment law

**Status, 9 November 2026:** new mathematical theorem for the source-derived **abstract two-counter P1 inverse shadow**, with a self-contained cylinder proof, an independent exact-integer regression, and Lean-checked universal arithmetic lemmas. Original-source Lean integration of the *statistical theorem* has not been completed; external novelty has not been assessed. Neither the original P1 machine nor BB(6) is decided.

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
- [`P1DyadicWidthCore.lean`](P1DyadicWidthCore.lean) is a locally checked, standalone Lean **arithmetic bridge**, not a kernel proof of the entire count. In Lean 4.36.0-rc2, `odd_slope_step`, `odd_root_slope`, `bit_flip`, `scaled_div`, and `child_affine` all compile with no `sorry`. Printed axioms are contained in `[propext, Quot.sound]`. `bit_flip` certifies the parity-bit flip on advancing a parameter by one modulus; `child_affine` certifies the exact affine slope transport without rational arithmetic.
- The shadow recurrence is already established as source-derived by the cited Agent 9 and Agent 13 work. This theorem is **about legal abstract inverse words**, not every original raw-machine transition. A uniform source-connected theorem lifting all bounded words at sufficiently high `q` has **not** been proved here. Do not claim that the unbounded abstract average transfers to actual blank-reachable machine states.
- Originality relative to external literature and priority over prior P1 shadow investigations remain to be independently reviewed. This is therefore maintained in `im-results/` rather than `results/`.

**Next decisive mathematical question:** quantify second moments or survival probabilities of the inverse-cylinder tree, and prove a source-connected, uniform-in-`q` lift for bounded-depth words. A proof that the survival probability tends to zero would be a much stronger **density-one** statement but would still require handling genuine non-odd exits before becoming a P1 halting decision.
