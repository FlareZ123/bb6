# Sharpened P1 all-count affine-wall gap: n >= 148 (original-source Lean certified)

## Formal verification update, 2026-11-05 22:55 UTC

**The entire conclusion is now proved against unchanged original P1 source in Lean 4.36.0-rc2.** [Manual CI 42125396876](https://github.com/FlareZ123/bb6/actions/runs/42125396876), job 127588157490, succeeded. Its final theorem
`BB6.Agent43Wall148Source.source_critical_wall_cost_above_n_plus_resets` in [CountedWall148Source.lean](CountedWall148Source.lean) composes the actual `CountCone`/original `inverseAt` and Agent50's SHA-verified source `WallCountLowerBound.lean`. Lean's final `#print axioms` is precisely `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no `native_decide`, no mock source.

The all-natural numerical gap `BB6.Agent43Numeric148.universal_numeric_gap_148` was separately checked in pure core Lean [CI 42125134569](https://github.com/FlareZ123/bb6/actions/runs/42125134569) and rechecked in the original-source CI. Proofs [NumericShell.lean](NumericShell.lean), [NumericPower148.lean](NumericPower148.lean), [NumericBridge148.lean](NumericBridge148.lean) use a five-endpoint exact-arithmetic bridge over n=148..511 and an infinite dyadic-shell induction for n>=512. This supersedes every earlier `pending` statement in the historical paper derivation below. The quantitative theorem remains a feeder restriction; no original P1 halting decision or BB(6) upper bound is established.



Agent 43, 2026-11-05. **New paper derivation pending an integrated original-source Lean theorem.** The key *counted last-positive-reset decomposition* is now independently original-source Lean kernel-checked at [manual CI 42120115832](https://github.com/FlareZ123/bb6/actions/runs/42120115832) (standard axioms only). The reset-tail power and mass facts are verified earlier by Agents 1 and 28. The numerical and composite theorem below have not yet been source-Lean certified. This improves the sufficient exponent threshold 194 in [WallAboveNPlusZ.md](WallAboveNPlusZ.md).

## Claim and exact scope

For every natural `n >= 148`, every genuine `CountCone (14*2^n - 2*n - 16) 3 b d m z` that ends at the affine wall `b = 4*(m+n)` satisfies **`m > n+z`**. The reset counter `z` is the source-defined count of positive-depth `inverseAt` steps. This is a necessary exclusion of a cost sector in one P1 inverse feeder. It proves no halting or nonhalting decision and no BB(6) upper bound.

We use Agent50's source-certified quantitative wall constraint `2^n <= 24^z*(n+2)^(2*z+2)` for `n>=42,z>=1` ([CI 42074258493](https://github.com/FlareZ123/bb6/actions/runs/42074258493)), and its wall-reset count `z>=4` for `n>=62`.

## Last-reset factor, retaining the actual z

Suppose contrary that `m<=n+z`; let `P=2^n`. By the newly certified `counted_cost_at_least_twice_resets`, `2*z<=m<=n+z`, so `z<=n` and `m<=2*n<=P`.

By the source-certified `counted_last_positive_reset`, split the actual *counted* history at its last positive inverse step of depth `t>=1`. Write `(bp,dp,mp,zp)` for its predecessor, `(2*k-4,c+4,m1)` for its successor, where `m1=mp+t+1`, and `s` for the following depth-zero suffix. The certificate preserves `z=zp+1`, gives `m1>=2*z`, and supplies a genuine `UpperTail`.

Original-source exact mass and power equations imply
```
bp + dp + 2*mp = 14*P - 2*n - 13,
dp + bp/2 + 3 = 2^t*(c+3).
```
Because `t>=1`, `bp/2<=bp`, and `mp>=0`,
```
2*(c+3) <= dp+bp/2+3 <= bp+dp+3
         <= 14*P - 2*n - 10.
```
Consequently `c+n+8<=7*P`. Outgoing source mass gives
```
2*k + c + 2*m1 = 14*P - 2*n - 13,
2*(k+4) + c + 2*m1 + 2*n + 8 = 14*P + 3.
```
As `m1<=m<=2*n` and `5*n<=P` (for all n>=5), these yield
```
2*(k+4) >= 7*P - 5*n + 3 >= 6*P,
k+4 >= 3*P.
```
The exact original-source `upper_tail_dyadic` theorem and wall equation give
```
2^s * (2*(m+n+3)) = k+4 >= 3*P,
m = m1+s,   s+2*z <= m <= n+z.
```
Since `s<=n-z`, cancellation of the positive factor `2^(n-z)` gives the **strengthened necessary restriction**
```
3*2^z <= 2*(m+n+3) <= 4*n+2*z+6.      (S)
```
For n>=148 and z<=n, (S) also implies `2^z<=4*n`.

## Exact all-natural arithmetic contradiction

We prove `24^z*(n+2)^(2*z+2)<2^n` under `n>=148` and (S), contradicting Agent50's certified necessity.

* **148<=n<=186:** (S) forces `z<=7`, since at z=8 the left is 768 and the upper bound is at most `4*186+2*8+6=766`; for larger z, exponential growth dominates the linear term by induction. Check exactly `24^7*150^16<2^148`. The inequality propagates as n grows because `(n+3)^16<2*(n+2)^16` for all n>=148; the ratio is decreasing and at the base `151^16<2*150^16`.
* **187<=n<=255:** (S) forces `z<=8`, since the case z=9 starts at 1536 while the upper bound is at most `4*255+18+6=1044`; the same induction excludes all greater z. Check `24^8*189^18<2^187`, and propagate using `(n+3)^18<2*(n+2)^18` for n>=187, verified at its base.
* **n>=256:** From `z<=n` and (S) obtain `2^z<=4*n`. The exact dyadic-shell proof in [WallAboveNPlusZ.md](WallAboveNPlusZ.md), Step 2, establishes `24^z*(n+2)^(2*z+2)<2^n` for all such n and z. Its u=8 split and u>=9 polynomial induction do not rely on n>=194.

For z<=7 or z<=8, replacement with the largest z in each finite shell increases `24^z*(n+2)^(2*z+2)` and is valid for every natural z. Therefore each shell gives the strict inequality and the wall history cannot satisfy `m<=n+z`.

The integer cutoff **148 is sharp for this particular arithmetic implication**: at n=147,z=7, the bound `3*2^z<=4*n+2*z+6` holds, but `24^7*149^16>=2^147`. This is not a real P1 witness.

## Exact verification and formalization boundary

Used JavaScript BigInt for exact checks:
```
24^7*150^16 = 301258172246400000000000000000000000000000000
2^148      = 356811923176489970264571492362373784095686656
24^8*189^18 < 2^187
151^16 < 2*150^16
190^18 < 2*189^18
```
A finite sweep of n=14..800 over all z satisfying (S) found the last arithmetic counterexample at n=147. This is a **smoke test**, separate from the universal induction proof above.

The source last-reset lemmas now passed unchanged-source Lean 4.36.0-rc2 CI [42120115832](https://github.com/FlareZ123/bb6/actions/runs/42120115832), with `#print axioms` only `propext`, `Classical.choice`, and `Quot.sound`. The remaining *formal* task is to compose original-source mass/power constraints with the factor theorem, prove (S), and formalize the universal numeric bound; until then this full threshold-148 theorem remains paper-level in `im-results/`. Seek independent novelty and error review before any `results/` promotion.
