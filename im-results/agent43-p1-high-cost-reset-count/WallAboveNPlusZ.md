# A stronger uniform affine-wall cost gap: m > n + z

**Agent 43, 2026-11-05 21:33 UTC. Source-shaped paper proof awaiting combined unchanged-source Lean CI.** This strengthens [WallBelowN.md](WallBelowN.md) in the large-exponent range and has a particularly short all-integer proof. The previously proved original-source Agent50 reset-count inequality is used as a black-box theorem.

## Statement

For every natural `n≥194`, every genuine `CountCone` from original P1 critical source

```
CountCone (14*2^n-2*n-16) 3 b d m z
```

whose last odd hub satisfies the low-cost affine wall `b=4*(m+n)` must obey

```
m > n+z.
```

Here `z` counts precisely the positive-depth original `inverseAt` steps; all arbitrarily interleaved zero-depth steps are included. In view of the original-source-certified Agent50 lower bound `z=Ω(n/log n)`, this yields the asymptotic necessary cost `m≥n+Ω(n/log n)` for **all counted affine-wall histories**, with no fixed cap on reset count.

The mathematical proof below is uniform; no finite enumerated cases beyond the single small dyadic shell are used. The combined statement is still at **paper proof** status until a new source-Lean axiom audit.

## Step 1: a source-specific last-reset estimate

Source mass coordinates `K=7·2^n−n−3`, `F=(b+12)/2`, `D=(d−1)/2`, satisfy `F+D+m=K+2`; each original odd inverse depth `t` has cost `l=t+1` and `2^l D'+m=K+D`. Every genuine `D'≥2`; each positive reset has `l≥2`, zero-depth steps halve `F`.

Agent50's unchanged-source theorem `source_critical_wall_needs_four_resets` gives `z≥4` for all n≥62. Choose the **last** positive reset, let `m_1≥2z` be outgoing cost, and `s=m−m_1` the final zero-depth suffix. Its outgoing mass satisfies

```
2F_1 ≥ 7·2^n−n−2m_1.
```

Suppose for contradiction `m≤n+z`. Since `m≥2z`, we have `z≤n` and hence `m_1≤m≤2n`. As `2^n≥5n/3` for n≥194, this yields `2F_1≥4·2^n`, so `F_1≥2^(n+1)`.

The final zero-depth suffix has `2^sF_{end}=F_1`; the wall has `F_{end}=2(m+n+3)`. Therefore

```
2^s(m+n+3) ≥ 2^n.
```

On the other hand `s=m−m_1≤m−2z≤n−z`, so

```
2^z ≤ m+n+3 ≤ (n+z)+n+3 ≤ 3n+3 ≤ 4n.       (★)
```

## Step 2: all-natural power inequality

**Elementary numerical theorem:**

```
∀ n z : Nat, 194≤n → 2^z≤4*n →
   24^z * (n+2)^(2*z+2) < 2^n.
```

First handle the finite-size bridge **`194≤n≤255`** uniformly: `2^z≤4n<1024` implies `z≤9`. At `n=194`, exact integer arithmetic gives `24^9·196^20<2^194`. For every `n≥194`, `(n+3)^20<2(n+2)^20` (compare its ratio with the exact base `197^20<2·196^20`), so induction propagates `24^9(n+2)^20<2^n` through `n=255`.

For **`n≥256`**, partition into dyadic shells: write `2^u≤n<2^(u+1)` with `u≥8`. From `2^z≤4n<2^(u+3)`, we obtain `z≤u+2`. Since `24<2^5`, we can replace `24^z` by `2^(5(u+2))`.

- **First shell `u=8`**, i.e. `256≤n≤511`: if `n≤509`, then `n+2<2^9` and
  ```
  24^z(n+2)^(2z+2) < 2^(5·10+9·22)=2^248 <2^256≤2^n.
  ```
  If `n∈{510,511}`, then `n+2<2^10`, so the same bound with `10·22` in place of `9·22` is `2^270<2^510≤2^n`.
- **All `u≥9`**: `n+2<2^(u+2)`, yielding
  ```
  24^z(n+2)^(2z+2)
     < 2^(5(u+2)+(u+2)(2u+6))
     = 2^(2u²+15u+22).
  ```
  The integer inequality `2u²+15u+22<2^u` holds at `u=9` (319<512) and persists by induction: the polynomial increases by `4u+17` per step whereas `2^u` at least doubles. Thus the preceding power is `<2^(2^u)≤2^n`.

This proves the numerical theorem for **every natural n≥194** and z satisfying (★), with no analytic logarithms or approximations. The threshold **194 is sharp for this numerical lemma**: at n=193,z=9, the hypothesis `2^9≤4·193` holds but `24^9·195^20≥2^193`. This sharpness says nothing about existence of a genuine P1 wall witness at n=193.

## Step 3: contradiction with a source-CI-proved universal inequality

Agent50's [original-source Lean theorem](../agent50-p1-two-reset/WallCountLowerBound.lean) was compiled in [CI 42074258493](https://github.com/FlareZ123/bb6/actions/runs/42074258493) and asserts for every genuine critical counted wall history with z≥1, n≥42:

```
2^n ≤ 24^z*(n+2)^(2z+2).
```

Our (★) and the numerical theorem force the strict reverse inequality, contradiction. Hence the asserted `m>n+z` for every n≥194.

## Scope and reproducibility

- This supplies an **entire cost sector** eliminated uniformly over unbounded reset counts. Its strength is asymptotically beyond the independent n≥62 theorem `m>n` in [WallBelowN](WallBelowN.md). For `62≤n<256`, use the previous weaker theorem.
- Previous certified contributions are Agent50's all-count inequality / n≥62 four-reset necessity and Agent28's source-connected scalar word grammar. The new source-shaped last-reset argument and dyadic shell proof are original to this note, subject to overlap review.
- **No unchanged-source Lean build yet verifies this composite statement**. Only the source inputs have such certification. Suggested Lean tasks: a generic source `CountCone` last-reset decomposition and the standalone all-natural dyadic shell numeric lemma. No dummy axioms, `sorry`, or `native_decide` should be accepted as formal completion.
- This still leaves wall candidates with `m>n+z`, high-cost exits `m>2^n`, and exceptional input `c=1`. It proves no P1 halt or nonhalt and no BB(6) upper bound.
