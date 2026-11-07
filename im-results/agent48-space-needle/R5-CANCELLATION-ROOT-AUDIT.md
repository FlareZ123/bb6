# r=5 cancellation feeder: exact computational no-parent audit

**Status:** exact, reproducible integer computation; **not yet Lean-kernel-certified**. This is an intermediate result and belongs in `im-results/`, not `results/`.

## Target

The cancellation family has
`v=(9^r+3)/2` and `K+1=r(9^r+5)`. At `r=5`,

- `v = 29,526`;
- `K = 295,269`;
- `q = (2^295269 - 3·2^29526 - 29529)/(2^29527+3)`, an integer;
- the shifted feeder target is `x = 2^29526(2q+3)`, with exactly 295,269 bits and `x < 2^K`.

The corresponding counter is `x-2 = oddTower(q,v)`. It is a synthetic terminal feeder in the exact terminal equation.

## Exact parent-divisibility reduction

Write `D_u=2^(u+1)+3` and `N_u=2x+3-2u`. If a one-step predecessor has valuation `u` and quotient `p`, the source recurrence gives
`x = D_u p + 3·2^u + u + 3`.
Equivalently,
`N_u = D_u(2p+3)`.

Thus every possible incoming parent requires `D_u | N_u`. Since `x<2^K` and a predecessor's shifted counter is at least `2^u` and strictly below `x`, every possible `u` lies below `K`. The audit checks the full conservative range `0 ≤ u ≤ K` (295,270 values).

This is the same exact inverse equation used by `NeedleGeneralInverse.parent_successor_iff`; `NeedleRootDecisionSource.finiteParents_spec` links that inverse relation to the pinned original-source high-level transition.

## Complete finite audit

The computation uses only Python standard-library arbitrary-precision integers.

1. **Small-prime rejection.** For each prime `p≤10,000`, find `L=ord_p(2)` and, when it exists, `e` with `2^e≡-3 (mod p)`. If `u≡e-1 (mod L)`, then `p|D_u`. A parent would also require `p|N_u`; if this fails, that valuation is rejected exactly. The script verifies both modular identities for every used prime.

2. **Low valuations.** For the remaining `u≤v`, test `N_u % D_u` using exact integer division.

3. **High valuations.** For `u>v`, put `B=2^(u+1)`, so `D_u=B+3equiv0` and `B≡-3 (mod D_u)`. Expand `N_u=Σ d_i B^i` with `0≤d_i<B`, and set `S=Σ d_i(-3)^i`. Then `S≡N_u (mod D_u)`. Here `K+1=10(v+1)`, `N_u<2^(K+1)`, and `u+1≥v+2`, so the expansion has at most ten digits. Consequently `|S|<B·3^10`. Since `3^11<B), if `D_u|S` then `|S|/D_u=k` satisfies `3k<B`, and therefore
`floor(|S|/B)=k`.
The exact divisibility test is consequently the integer equality
`|S| = floor(|S|/B)·(B+3)`.
This avoids a large integer division for the high-valuation survivors.

## Result

| Check | Count | Outcome |
|---|---:|---|
| Possible valuations checked | 295,270 | `0…295,269` |
| Prime moduli considered | 1,229 | `p≤10,000` |
| Useful `(p,L,e)` witnesses | 685 | all modular identities checked |
| Rejected by a prime witness | 238,684 | exact contradiction |
| Low survivors | 5,710 | all exact divisions nonzero |
| High survivors | 50,876 | all signed-remainder tests nonzero |
| High signed-digit maximum | 10 | matches the bound |
| Independent direct high checks | 256 | all agree |

**No valuation `u≤K` satisfies `D_u|N_u`.** Hence this r=5 synthetic feeder has no incoming high-level parent. Because it is not the initial counter, it cannot lie on the genuine blank-start orbit.

The deterministic audit script is [`r5_cancellation_parent_audit.py`](r5_cancellation_parent_audit.py). It prints the complete counts and SHA-256 digests for the rejection set, witness map, and high-survivor set. Re-run with:

```text
python3 r5_cancellation_parent_audit.py
```

## Mathematical status and next step

This resolves the fifth cancellation-family feeder at the exact computational level, extending the four previously kernel-checked exclusions by one. The remaining gap is formalization: prove the modular-witness sieve and signed base-`B` reduction in Lean, then connect the resulting no-parent theorem to `ReachN` through `NeedleRootDecisionSource`. Do not yet cite this as a Lean theorem or as a solution of the unbounded cancellation family. The square-root-bounded terminal-feeder sector and all `r≥6` members remain open.
