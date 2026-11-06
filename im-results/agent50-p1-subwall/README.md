# Original-source all-count P1 last-reset inequalities below an adjustable left wall

**Agent50, 2026-11-06 01:57 UTC. Intermediate mathematical result.** This is a true source-connected Lean theorem, not a P1 halt/nonhalt decision or a global BB(6) bound. Independent outside novelty is unassessed; retain in `im-results/`.

## Theorem and precise domain

Set `P=2^n`, `n>=14`. For arbitrary natural left offset `r`, every original (unmodified) source `BB6.Agent28.CountCone (14*P-2*n-16) 3 b d m z` satisfying `z>=1`, `b<=4*(m+n+r)` and `m<=P` obeys

```
2^(n+2*z) <= 2^m*(m+n+r+3).
```

There is **no bound on the length of the inverse history, the number z of positive-depth resets, the number of zero-depth edges, or the right endpoint d**. The source count is the exact witness count, with no collapse of multiple paths to the same endpoint.

The `r=0` special case recovers the previously paper-level last-reset tradeoff of [Agent43](../agent43-p1-high-cost-reset-count/LastResetTradeoff.md) and extends it from equality `b=4*(m+n)` to all `b<=4*(m+n)`. A separate **all-natural specialization** uses the genuine even-exit small-left width:

```
q>=1, z>=1, n=16*q+2,
b<=4*m+192*q+40, m<=2^n
    => 2^(n+2*z)<=2^m*(m+48*q+13).
```

The latter is a necessary restriction whenever an original candidate has an authenticated small-left condition. The theorem itself does not assert that a blank-reachable exit exists or that all exits satisfy that condition. The high-cost alternative `m>2^n` remains.

## Mathematical proof

Use the original `counted_last_positive_reset` factorization from Agent43: a counted source prefix ending at `(bp,dp,mp,zp)`, one final positive `inverseAt bp dp t = some (k,c)` with `t>=1`, followed by an unrestricted `UpperTail` of length `s`. Preserve exact identities `m=mp+t+1+s`, `z=zp+1`, and `2*z<=mp+t+1`. The source `OddCone` mass and `inverseAt_iff_power_mass` give

```
c+n+8<=7*P
2*k+c+2*(mp+t+1)=14*P-2*n-13.
```

As `mp+t+1<=m<=P` and `n<=P`, these imply `k+4>=2*P`. The exact original `upper_tail_dyadic` statement is `2^s*(b+12)=2*(k+4)`. Hence under `b<=4*(m+n+r)`,

```
P <= 2^s*(m+n+r+3).
```

Multiplying by `2^(2z)`, using `2z<=mp+t+1` and the exact source cost equality, yields the theorem. All arithmetic uses natural numbers and no transcendental/log estimates.

## Verification / traceability

- [Arithmetic.lean](Arithmetic.lean), kernel-checkable arithmetic including arbitrary `r`.
- [SubwallSource.lean](SubwallSource.lean), source-connected bounded-cost reset output lower bound, subwall case, arbitrary `r`, and the `192q+40` specialization.
- [Manual-only workflow](../../.github/workflows/agent50-p1-subwall-source.yml) directly compiles unchanged `Agent1`, `Agent47`, `Agent28`, `Agent43` original source definitions. It intentionally has no per-commit trigger.
- **Successful original-source CI [42146597041](https://github.com/FlareZ123/bb6/actions/runs/42146597041)** first verified `r=0`.
- **Successful original-source CI [42146998575](https://github.com/FlareZ123/bb6/actions/runs/42146998575)**, head `a731170e5a0fe0f603ae6dc7d6fec74331edb495`, job 127660779648, independently verifies the arbitrary-offset and small-left specialization. All terminal `#print axioms` are exactly subsets of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, mock source, or `native_decide`.

Agent43 previously gave the last-reset cost tradeoff on paper for exact wall equality; see [LastResetTradeoff.md](../agent43-p1-high-cost-reset-count/LastResetTradeoff.md) and [SubwallExtension.md](../agent43-p1-high-cost-reset-count/SubwallExtension.md) for related ideas and priority. This source certification makes the offset-uniform argument independently reusable.

## Next questions

1. Combine the bound with source-authenticated necessary gates for the real **entire** even-exit branch to exclude a whole infinite family, rather than merely lower-bound its cost.
2. Derive a quantitative reset-count lower bound for arbitrary `b<=4(m+n+r)`, analogous to the original exact-wall Agent50 inequality `2^n<=24^z(n+2)^(2z+2)`. That exact-wall proof uses equality essentially; do not assume it already transfers.
3. Investigate the complementary `m>2^n` sector and the exceptional-right-coordinate exit. The present theorem does not constrain them.

**Research status:** a new source-verified, fully quantified necessary obstruction; no six-state machine classified, no exact BB(6) value.
