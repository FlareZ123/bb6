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

5. **Exact final-reset classification for the exceptional right-five terminal under a 5/2 exponential budget** [ExceptionalLastResetDepthSource.lean](ExceptionalLastResetDepthSource.lean): for `n>=14,z>=1`, a genuine source `CountCone (14*2^n-2*n-16) 3 b 5 m z` satisfying `2*m+n+2<=5*2^n` has a last positive reset with zero upper-tail length and exact depth `t=n+1`, with source counter `c=1`. If `(bp,dp,mp,zp)` is the prefix hub and `k` is the inverse parameter, the exact identities are
   ```
   z = zp+1
   b = 2*k-4
   k+m+n+7 = 7*2^n
   bp+4*m+12 = 12*2^n
   dp = 2*2^n+2*m+3
   mp+n+2 = m.
   ```
   This is a structural theorem about the source inverse cone. It does not assert that the terminal state is actually blank-reachable or close the exceptional branch. The manual source CI [42252893616](https://github.com/FlareZ123/bb6/actions/runs/42252893616) recompiles the original dependencies and explicitly rejects `sorryAx` in the theorem's axiom audit.

All compilation used [manual-only source workflow](../../.github/workflows/agent50-p1-subwall-source.yml) with unchanged, real original P1 modules and SHA-checked archived reset sources; no mock `CountCone`, `sorryAx`, `native_decide`, or fabricated proof imports. The exact-depth proof imports the already compiled `CountedWallStrongGateSource` directly and reconstructs the last-reset argument; it deliberately does not depend on Agent43's currently non-elaborating `ExceptionalLastResetSource.lean` draft. These are **mathematically proved necessary conditions for inverse histories**, not a reachability or halting classification, not a claim of P1 nonhalting, and not a universal BB(6) upper bound. The exact academic novelty relative to external literature is unassessed, and the work remains `im-results/` pending independent review. Agent43's preceding exact-wall proofs and paper subwall observations retain intellectual priority for the shared structural approach.

## Next questions

1. Extend the exact right-five last-reset classification beyond `2*m+n+2<=5*2^n`; above this budget a zero-depth tail may reappear and the final inverse depth need not be `n+1`.
2. Find a source-to-trace bridge for the exceptional `c=1` branch. The exact-depth theorem classifies a `CountCone` witness and must not be mistaken for reachability of its endpoint.
3. Combine the all-width subwall inequalities with authenticated gates for the full even-exit branch, then investigate the complementary high-cost `m>2^n` sector.

**Research status:** a new source-verified, fully quantified necessary obstruction; no six-state machine classified, no exact BB(6) value.

## Additional certified original-source results, 2026-11-06 02:29 UTC

These results supersede the earlier "next questions" section. They were completed, kernel-checked and source-audited after the first tradeoff theorem. All formulas refer to **exact source `BB6.Agent28.CountCone (14*2^n-2*n-16) 3 b d m z`**, unrestricted inverse history depth, finite positive-reset count `z` preserved faithfully, and natural counters.

1. **All-cost subwall logarithmic obstruction** [SubwallLog.lean](SubwallLog.lean): for `n>=14`, every genuine `OddCone` ending at `b<=4(m+n)` satisfies `2^(n-m)<n`. This generalizes the original exact-wall theorem. The weaker condition `K<=D+3m+2n+4`, rather than exact equality, suffices for the dyadic word invariant. Original-source CI [42148404771](https://github.com/FlareZ123/bb6/actions/runs/42148404771) succeeded.
2. **All-reset polynomial count obstruction for the full subwall** [SubwallBudget.lean](SubwallBudget.lean): for `n>=42,z>=1`, `b<=4(m+n)` implies `2^n<=24^z*(n+2)^(2z+2)`, independent of `m`. The actual [CountFinal source](../agent50-p1-two-reset/WallCountLowerBound.lean) and `ResetSkeleton` were recompiled from SHA-256 checked archives. CI [42148943487](https://github.com/FlareZ123/bb6/actions/runs/42148943487) succeeded.
3. **Source-certified n>=148 all-count strict cost gap throughout the subwall**: [SubwallNear.lean](SubwallNear.lean) proves `3*2^z<=2*(m+n+3)` if `n>=14,z>=1,m<=n+z,b<=4(m+n)`; this combines with the original n>=148 exact universal numeric bridge and (2) to exclude `m<=n+z` whenever `z>=1`. [ZeroArithmetic.lean](ZeroArithmetic.lean) proves separately that a zero-positive-reset upper tail with `m<=n` has `2^m<=2*(n+2)`. [SubwallAllCount.lean](SubwallAllCount.lean) combines that divisibility bound, original source logarithmic gap and the original octic growth bound to handle `z=0`. Consequently the final original-source theorem
   ```
   n>=148, CountCone critical b d m z, b<=4*(m+n) => n+z<m
   ```
   holds for **all natural z including zero**. Original-source CI [42149985248](https://github.com/FlareZ123/bb6/actions/runs/42149985248), job 127670590246, succeeded; the final `#print axioms` audit has only `propext, Classical.choice, Quot.sound` and no other axioms. This directly strengthens Agent43's originally proved `b=4(m+n)` cost gap to the entire below-wall region.
4. **All-width, all-reset necessary polynomial count bound** [OffsetLog.lean](OffsetLog.lean), [OffsetBudget.lean](OffsetBudget.lean): for `n>=42, r>=0, z>=1`, every genuine `CountCone` with `b<=4*(m+n+r)` must satisfy
   ```
   2^n <= 24^z*(n+2)^(2*z+1)*(n+r).
   ```
   The source odd-word cost gap is `2^(n-m)<n+r`. This proof reuses the original exact `ResetSkeleton.invariant` and carries its polynomial cost envelope through the offset parameter with no bound on `m`. The explicit P1 small-left specialization for `n=16q+2,q>=3`, `b<=4*m+192*q+40`, is
   ```
   2^(16*q+2) <= 24^z*(16*q+4)^(2*z+1)*(48*q+10).
   ```
   Source CI [42150387600](https://github.com/FlareZ123/bb6/actions/runs/42150387600), job 127671935624, succeeded; all terminal axiom audits contain standard Lean axioms only.

All compilation used [manual-only source workflow](../../.github/workflows/agent50-p1-subwall-source.yml) with unchanged, real original P1 modules and SHA-checked archived reset sources; no mock `CountCone`, `sorryAx`, `native_decide`, or fabricated proof imports. These are **mathematically proved necessary conditions for inverse histories**, not a reachability or halting classification, not a claim of P1 nonhalting, and not a universal BB(6) upper bound. The exact academic novelty relative to external literature is unassessed, and the work remains `im-results/` pending independent review. Agent43's preceding exact-wall proofs and paper subwall observations retain intellectual priority for the shared structural approach.


## Exact exceptional right-five reset-depth window widened (Agent 43, 2026-11-06 21:20 UTC)

The earlier exact two-depth theorem used the budget
`2*m+2*n+7 <= 7*2^n`. Agent 43 removed the duplicated tail argument by reusing the unconditional original-source theorem `source_right_five_last_positive_reset_no_tail`, then widened the source-certified budget to

```
n >= 14
z >= 1
CountCone (14*2^n-2*n-16) 3 b 5 m z
2*m+2*n+7 <= 10*2^n.
```

The original-source theorem `source_exceptional_last_reset_two_depths` now proves that the last positive reset has zero upper-tail length, input counter `c=1`, and exactly one of two depths. For a genuine prefix hub `(bp,dp,mp,zp)` and inverse parameter `k`, the shared identities are

```
z = zp+1
b = 2*k-4
k+m+n+7 = 7*2^n.
```

The two exhaustive cases are

```
t = n:
  inverseAt bp dp n = some (k,1)
  bp + 4*m + 16 = 20*2^n
  dp + 6*2^n = 2*m + 5
  mp + n + 1 = m
  3*2^n - 2 <= m

t = n+1:
  inverseAt bp dp (n+1) = some (k,1)
  bp + 4*m + 12 = 12*2^n
  dp = 2*2^n + 2*m + 3
  mp + n + 2 = m
  m <= 3*2^n - 5.
```

Thus the two costs `m=3*2^n-4` and `m=3*2^n-3` are impossible in this source cone. This widens the exact reset-depth classification well beyond the earlier `2*m+n+2 <= 5*2^n` (approximately `m<=2.5*2^n`) refinement. The result is still a necessary condition on an inverse-history witness. It does not establish that the prefix hub or terminal is blank-reachable, and it does not decide P1 or BB(6).

**Verification:** successful original-source Lean CI [42295780908](https://github.com/FlareZ123/bb6/actions/runs/42295780908), head `7e16c0e9372b01b101fd26e029fe6dbdd6f3882d`. The terminal axiom audit for `source_exceptional_last_reset_two_depths` is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The run compiled the unchanged original P1 source dependencies and the new theorem. The earlier Agent50 no-tail and mid-cost exact-depth theorems also compile in the same workflow.
