# Positive density of first-even Sheep states with no incoming edge

**Agent 17, 2026-11-05. Intermediate mathematical result,** conventional elementary all-parameter proof plus exact rational inclusion-exclusion. The published/source-checked Sheep one-variable even return is used without alteration; its original-machine semantics were independently certified in [Agent 16's source workflow](../agent16-sheep-even-return/README.md). This is a global fact about the synthetic/legal even-state graph, not a decision of the actual blank-origin orbit, the Sheep holdout, or BB(6). No external academic-novelty claim; keep in `im-results/`.

## Theorem

Define the legal *first-even Sheep return* `E(x)` on each nonterminal even section state `x=2^b v`, `b>=1`, odd `v>=3`, by the established Sheep section law:

```text
F(x) = x+b+3            (v=3)
F(x) = x+b+(v-1)/2      (v>=5).
F(x)-1=2^h*w, w odd;    E(x)=1+3^h*w.
```

Let `D\\subseteq\\mathbb{N}_{>0}` consist of those positive integers `t` for which the even target `6t` has **no** legal even first-return predecessor. Then **the natural density `\\delta(D)` exists** and lies in the explicit rigorously certified interval

```text
0.48523956636605564 < density(D) < 0.48524528841195410.
```

Here density is measured among indices `t`, equivalently among all multiples of six. In particular **over 48.5239% of positive multiples of six have no incoming E edge**. This implies that the lower asymptotic density of the no-incoming even section counters among *all positive integers* is at least `0.48523956636605564/6 > 0.08087326`. Among even integers it is at least one-third of the displayed conditional fraction. These latter statements are **lower bounds**; we do not assert that the density of all no-incoming even counters exists.

The endpoints are exact rational numbers from [density_certificate.py](./density_certificate.py):

```text
lower = 166438886461775438421248827067 / 343003534745179991411112017920
upper = 317460726058472779546624 / 654227323046073897192215 .
```

The elementary non-computer lower bound `density(D) >= 317/840` follows directly from the convergent reciprocal-modulus union bound. The narrow displayed numerical interval additionally uses a finite twelve-progression inclusion-exclusion calculation.

## Exact characterization of possible generic predecessors

A target `y=6t` is divisible by three. If `E(x)=y`, its hidden odd-block length must be `h=0`, because `1+3^h w\\equiv1\\pmod3` when `h>0`. Therefore `F(x)=6t`.

For a generic source `x=2^b v` with `b>=1` and odd `v>=5`, the predecessor equation is

```text
12t = (2^(b+1)+1)*v + 2b-1.
```

Let `M_b=2^(b+1)+1` and `g_b=gcd(12,M_b)`. The congruence `12t \\equiv 2b-1\\pmod{M_b}` is solvable exactly when `g_b | (2b-1)`. Because `M_b` is odd, `g_b\\in\\{1,3\}`. When `b` is odd, `g_b=1` and the congruence is always solvable. When `b` is even, `g_b=3`, so solvability is equivalent to `b\\equiv2\\pmod3`, equivalently `b\\equiv2\\pmod6`.

For every permitted `b`, the source equation is equivalent to the **one arithmetic progression**

```text
t ≡ r_b (mod m_b),
m_b = M_b/g_b,
r_b = ((2b-1)/g_b) * (12/g_b)^(-1) (mod m_b).
```

Conversely, whenever `t` belongs to this progression and is sufficiently large (depending on the fixed `b`), the quotient

```text
v=(12t-2b+1)/M_b
```

is a positive odd integer at least five. This gives a genuine legal source `x=2^b v` with `F(x)=E(x)=6t`. Oddness is automatic because the numerator and denominator are odd. Each progression thus equals a genuine generic-source incoming family apart from finitely many small `t`.

Exceptional `v=3` sources contribute at most `O(log X)` targets `6t\\le X`: the output `3\\cdot2^b+b+3\\le X` forces `b=O(log X)`. They have natural density zero and do not affect the theorem.

## Why the infinite union has a density

There are only `O(log X)` eligible `b` for sources returning a target `6t\\le X`, because each legal source has `x>=3\\cdot2^b` and the return strictly increases its counter. The number of `t\\le T` in a fixed progression `r_b\\pmod{m_b}` is `T/m_b+O(1)`. For any fixed cutoff `B`, the large-`b` contribution to the *fraction* of indices `t\\le T` is bounded as `T\\to\\infty` by

```text
sum_{b>B} 1/m_b <= sum_{b>B} 3/2^(b+1) = 3/2^(B+1).
```

This upper bound tends to zero with `B`. Each finite union of progressions is periodic and hence has an exact rational density. The finite union densities increase monotonically, and the geometric tail makes their limit equal to the actual density of the full generic-parent set. The exceptional-source family and the finitely many small-target deviations per `b` have zero asymptotic density by the same `O(log X)` estimate. Thus the no-incoming set `D` has a well-defined natural density.

For an independent elementary explicit bound, sum admissible `b` contributions:

```text
sum_{odd b>=1} 1/m_b
 < 1/5 + sum_{odd b>=3} 2^(-b-1)
 = 1/5 + 1/12 = 17/60,

sum_{b=2+6j, j>=0} 1/m_b
 < 1/3 + sum_{j>=1} 3*2^(-b-1)
 = 1/3 + 1/168.

Therefore parent density < 523/840,
and no-incoming density > 317/840.
```

The first inequality's bound is strict because `M_b>2^(b+1)`; the second isolates `b=2`, where `1/m_2=1/3`.

## Fully exact arithmetic certificate and numerical scope

The deterministic standard-library-only [density_certificate.py](./density_certificate.py) takes cutoff `B=18` and computes the **twelve** admissible source congruence classes:

```text
b = 1,2,3,5,7,8,9,11,13,14,15,17.
```

A collection of congruences `t\\equiv r_i\\pmod{m_i}` is simultaneous-solvable if and only if every pair's residues agree modulo the pairwise gcd. When solvable, generalized CRT makes its exact density `1/lcm(m_i)`. The script enumerates all `2^12-1` nonempty subsets, finds **287** compatible subsets, and computes the finite union density by rational inclusion-exclusion:

```text
S_18 = 336766596987601117645591 / 654227323046073897192215
     = 0.514754711588046...
```

The full generic parent density lies between `S_18` and `S_18+3/2^19`. Taking complements gives the rational interval above. The upper endpoint is strict: a genuine b=19 predecessor has t=1660250, corresponding to x=9961472 and E(x)=9961500. This t lies in the b=19 progression and outside all twelve b<=18 residue progressions, as directly checked by density_certificate.py. The resulting residue cylinder has positive density, so the true parent density is strictly larger than S_18. The lower endpoint is strict because each reciprocal modulus in the omitted tail is strictly below its geometric upper estimate. The calculator uses exact `fractions.Fraction`; no floating-point values enter the proof assertions. It independently asserts the finite rational numerator and denominator, the number of classes and compatible subsets.

As an **independent finite sanity check**, enumerating all legal even sources `x\\le10^6` and marking their outputs divisible by six gives **80,880 no-incoming targets out of 166,666 multiples of six**, ratio `0.48528194...`, consistent with but not a premise of the asymptotic theorem. Finite fluctuations need not lie inside the limiting interval.

## Relationship to the BB(6) objective

The theorem reveals a high-density family of global *garden-of-Eden* even section states. It provides a reusable arithmetic obstruction for constructing forward invariant languages and explaining why many synthetic targets can never occur even from arbitrary starts. It is far stronger in ordinary counting density than the fourteen infinite geometric rays recorded in [README.md](README.md), but does not itself exclude the genuine power-of-two halting gates (which are coprime to three), decide the true blank-10 orbit, or prove any BB(6) bound. To convert it into a halting decision requires a genuine seed-sensitive argument connecting all surviving power gates to forbidden ancestors, a missing premise that must be proved independently.

**Source and novelty boundary:** Only the pre-existing F/E formula's original-machine equivalence is source-kernel-certified. The new counting theorem has a complete conventional mathematical derivation and exact arithmetic certificate, without a Lean implementation of the full density argument, independent peer review or external novelty check.