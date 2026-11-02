# Three all-index Sheep even-return exclusions, with one reusable modular inverse certificate

Agent 40, 2026-11-02. **Intermediate research.** This arithmetic certificate concerns the `SheepEven.EvenReach 10` graph defined and formally linked to the *original* six-state Sheep Turing machine by Agent 16 (successful original-source Lean CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547)). Neither the Sheep holdout nor BB(6) is decided. The new inverse-certificate arithmetic has **not** been fully formalized in Lean; it is a written all-quantifier argument plus a standard-library-only executable certificate. Novelty outside this repository has not been established.

## Uniform exclusions

Let `E` be Agent 16's exact first-even-return map on nonhalting even Sheep section states, starting at the actual even entry 10. For each row and **every** natural `k`,

`¬ SheepEven.EvenReach 10 (2^(r + M*k))`.

| r | M | Complete symbolic predecessor tree |
| ---: | ---: | --- |
| 648 | 53,591,297,760 | `2^j ← (2^(j+8)−1228)/2187 ← ∅` |
| 864 | 14,594,696,756,640 | `2^j ← (2^(j+10)−16576)/3483 ← ∅` |
| 1002 | 89,318,829,600 | `2^j ← {(2^(j+3)−2)/15, (2^(j+5)−68)/81} ← ∅` |

Each arrow points **backward** against `E`. An empty inverse set holds for every exponent in the arithmetic progression, without a time horizon. The root and all displayed possible parents are integers greater than 10 for every `k≥0`. The progressions are pairwise disjoint (their differences in `r` are nonzero modulo the pairwise gcd of the periods). Independent exact integer inversion at the base indices `j=r` matches every displayed tree. At these three base indices, the ordinary unaccelerated `F` inverse tree remains open at depth five, whereas the `E` inverse tree closes at depth two. These families differ from Agent 14's four previously recorded `r mod 4860` families; no exhaustive novelty claim is implied.

## Exhaustive symbolic inverse argument

For any symbolic target `Y=(2^(j+s)+b)/d`, where `s≥0`, `b∈ℤ`, and `d` is positive odd, every even `E` predecessor `t` factors through an odd-run length `h≥0`:

```
Y = 1 + 3^h*u
z = F(t) = 1 + 2^h*u
D = d*3^h
C = 2^h*(b-d)+D
z = (2^(j+s+h)+C)/D .
```

Here `F` is the certified section map, `t=2^a*v`, `a≥1`, with odd `v≥3`. The `v=3` branch is exceptional, `z=3*2^a+a+3`. For the generic `v≥5` branch, the exact equation is

```
D*(2^(a+1)+1)*v = 2^(j+s+h+1)+B
B = 2*C-D*(2*a-1).
```

Thus `D | 2^(j+s)+b-d` and the following **necessary** generic parity test holds, with `T=D*(2^(a+1)+1)`:

```
(2^(j+s+h+1)+B) mod (2*T) = T .
```

A surviving pair `(h,a)` has the **unique possible** parent expression

```
t = [2^(j+s+h+1+a)+2^a*B] / T,
child(s,b,d,h,a)=(s+h+1+a,2^a*B,T).
```

The checker retains all candidates passing these necessary conditions even if further admissibility conditions could exclude them; this conservative direction is sound for proving nonreachability.

### Unbounded `h`: an actual modular witness

For each node, `certify.py` finds a finite `H` satisfying

```
(2^(r+s)+b-d) mod (d*3^H) != 0,
2^M mod (d*3^H) = 1 .
```

Therefore the same nondivisibility holds at **every** `j=r+Mk`, ruling out all `h≥H`. This uses only the displayed modular exponentiations; no presumed multiplicative-order oracle is trusted.

### Unbounded `a`: exact residue gap

For each `h<H`, set `Q(a)=D*(2*a-1)-2*C`, always odd. The checker finds an `A` with `1<Q(A)<2^A` and `2D<2^A`. Both strict inequalities propagate to every `a≥A` since `Q(a+1)=Q(a)+2D` and `2^(a+1)=2*2^a`. The generic equation would force

`2^(j+s+h+1) ≡ Q(a) (mod 2^(a+1)+1)`.

But positive powers of two modulo `2^(a+1)+1` have representatives `+2^e` or `-2^e` for `0≤e≤a`. None lies at an **odd** integer strictly between 1 and `2^a`. This eliminates every `a≥A`. Agent 40 previously formalized this unrestricted residue-gap lemma in Lean at [ResidueGap.lean](../agent40-sheep-third-preimages/ResidueGap.lean), and Agent 14 separately formalized uniform cutoff propagation [HighBound.lean](../agent14-sheep-even-inverse/HighBound.lean).

### Exceptional `v=3`: exact all-exponent inequality

For `n=j+s+h`, the exceptional equality becomes

`2^n = c*2^a+D*(a+3)-C`, where `c=3D`.

Write `e=bit_length(c)`, so `2^(e−1)<c<2^e`. The checker verifies for the minimal `n=r+s+h`:

```
n >= e+2
(2^e-c)*2^(n-e) > D*(n+3)+abs(C)
2^(n-e) > 2D
D*(n-e+4) >= C .
```

These bounds persist as `n` increases: the exponential terms double, the linear RHS increases by at most `D`, and the last inequality strengthens. For `a≤n-e`, the first inequality makes `2^n-c*2^a>D*(a+3)-C`. For `a≥n-e+1`, already `c*2^a>2^n`, and `D*(a+3)-C≥0). Hence the exceptional branch is impossible for every `a≥1` at every allowed exponent. Compare Agent 14's independently explained exceptional inequality in [UNIFORM-138.md](../agent14-sheep-even-inverse/UNIFORM-138.md).

### Low `a`: exact modular period verification

The checker evaluates **all** finitely many pairs `0≤h<H`, `1≤a<A(h)`. For every such pair it independently asserts `2^M mod D=1` (when `D>1`) and `2^M mod T=1`. All exponents in the parity test are positive, so congruence of powers modulo odd `T` extends to congruence modulo `2T` by evenness. Consequently the truth of both necessary congruences is **constant for every** `j=r+Mk`; testing `k=0` exhausts the infinite progression. The program exactly matches the hard-coded surviving pair-to-child maps and recursively checks that the children have **no** possible parents.

The entire finite tree excludes `E`-reachability by considering the last edge of any path from 10. The target itself and its complete candidate parent set are greater than 10, and every candidate parent has empty inverse fiber. This contradicts a path from 10. Composing with Agent 16's already source-certified `raw_halts_iff_even_power` yields three real necessary halting-exponent exclusions for the original Sheep machine, conditional on the arithmetic certificate's soundness.

## Reproduction and validation boundary

Run `python certify.py` (Python 3.10+, standard library only). It prints `PASS` for all three families. The script checks the modular period witnesses, every low-`a` exclusion, the unbounded-`a` gap start, the entire unbounded-`h` cutoff, all special-branch inequalities, child identities, node integrality, and an **independently implemented finite inverse enumerator** at each base exponent. It never evaluates `2^(r+Mk)` for positive `k` and does not rely on finite forward simulation as proof of a universal statement.

This is a new reusable inverse-certificate construction and three additional periodic exclusions **within this repo**. The proof remains in `im-results/` because the new universal conclusions are not yet represented by an end-to-end Lean kernel theorem, and no BB(6) upper bound or holdout decision follows. Next work: produce a generic Lean checker that reflects these exact period witnesses, high-valuation bounds and recursive inverse tree into a source-connected all-time theorem; assess whether the same E-based construction can form a useful forward invariant rather than another sparse residue catalog.
