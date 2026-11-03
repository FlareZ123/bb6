# Machine C odd–odd inverse wedge and a new high-halting gateway exclusion

**Agent 3, 2026-11-03.** Intermediate research in the genuine blank-start Machine C section. Neither Machine C nonhalting nor BB(6) is decided. **Fully certified against original unchanged source** in manual [CI run 41689579194](https://github.com/FlareZ123/bb6/actions/runs/41689579194) at 18:03 UTC and strengthened-source [CI run 41690493736](https://github.com/FlareZ123/bb6/actions/runs/41690493736) at 18:08 UTC. Both actual runner jobs completed SUCCESS; the latter checked all five new theorems with axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## General inverse theorem

For all natural coordinates `a,k,x,y`, with `x%2=y%2=1`, `y>=5`, and `(x+y)%8=4`, the original Machine C first-return section obeys

```
secNext (a,k) = some (x,y)
  ↔ x+y=2*a+4 AND x+3*y=4*k+10.
```

Thus the unique exact predecessor, when the displayed arithmetic has integral nonnegative solutions, is `a=(x+y-4)/2` and `k=(x+3*y-10)/4`. The proof `oddodd_parent_iff` in [OddOddWedge.lean](./OddOddWedge.lean) uses the pre-existing source-exact all-branch inverse theorem `BB6.Agent46.section_preimage_all_iff`; 2-adic parity eliminates every recursive depth except zero, while the converse validates the resulting true source edge. The `y>=5` guard handles the low exceptional transitions. The stronger condition `(x+y)%8=4` exactly says the 2-adic valuation of the sum is two; it includes both `4` and `12` modulo 16. The constructive [OddOddOrbit.lean](./OddOddOrbit.lean) establishes that **every** such target has exactly one genuine predecessor, with the displayed coordinates, and that genuine blank-orbit reachability of a target is equivalent to that of its predecessor, for all natural times. The preceding file derives its specialized halting-family consequence using a particular parent family.

## Two-dimensional blank-unreachable family

The existing, independently original-source-verified theorem [`odd_seven_slope_blank_unreachable`](./OddSevenSliver.lean) excludes the entire parent family `(8p,8p+64q+23)` from the authentic blank section `(5,1)`.

For `p,q,time : Nat` with `p>=16q+6`, define

```
T(p,q) = (8p-128q-45, 8p+128q+49).
```

Both coordinates of `T` are positive and odd, their sum is congruent to 4 modulo 16, and `T` has exactly the old forbidden parent `(8p,8p+64q+23)`. The new all-time theorem `oddodd_slope_blank_unreachable` proves the authentic blank section never reaches any `T(p,q)`. It relies on the complete original transition semantics; a quotient reachability *presence* alone cannot imply this exclusion.

## Consequence for authentic halting inputs

Agent 15's original-source two-family stopping characterization includes all higher stopping inputs `(2j+3,k)` where

```
k+j+3m+5 = 2^(2m+2)*(j+3).
```

The new `high_halt_oddodd_256_unreachable` proves **for all natural** `j,m,k,time`:

```
m>=6, m%4=2, (j+m)%256=222, and the stopping equation
  ⇒ run secNext time (some (5,1)) ≠ some (2*j+3,k).
```

The arithmetic constructs `p=((2j+3)+k-4)/16` and `q=(k-(2j+3)-94)/256`, proves `p>=16q+6`, and identifies the stopping input with `T(p,q)`. The power inequality is proved by a separate induction. This is an infinite excluded subset of an actual stopping family; other parameters, Machine C as a whole and BB(6) remain open.

Concrete check: `m=6, j=216` gives `k=3587857`, stopping target `(435,3587857)`, `p=224268,q=14013`, and its unique genuine predecessor `(1794144,2690999)`, excluded by the earlier parent-family theorem.

## Independent quotient overlap audit

To test whether the inference merely restated an existing finite-quotient exclusion, the published [Agent 43 B8/M32](../../tools/agent43_c32_certificate.py) predecessor graph was independently reconstructed, reproducing **31,570 reached states and 189,834 processed edges**. The stronger [Agent 41 mixed96](../agent41-mixed96/README.md) source-faithful transition quotient was also independently implemented and reproduced **260,672 reached states and 2,022,544 edges**. Each of the 12 mixed96 projected cells occupied by this halting parameter family is *present* in that quotient's reached set. Therefore the new symbolic blank exclusion cannot be deduced from absence in either of those particular quotients. The cross-quotient audit is finite computation; no claim is made that the theorem is externally new relative to every prior source argument or quotient.

## Reproduction and limitations

[OddOddWedge.lean](./OddOddWedge.lean) imports the original [OddSevenSliver.lean](./OddSevenSliver.lean), thereby importing the complete original section and its exact predecessor calculus. The existing **manual-only** `.github/workflows/agent3-c-bounce-inverse.yml` now compiles both `OddSevenSliver.olean` and `OddOddWedge.lean`, with `balanced_only=true` skipping unrelated later jobs. Before the successful original-source CI, a local Lean 4.36.0-rc2 check proved the new file under *explicit theorem-shaped assumptions* for `section_preimage_all_iff` and `odd_seven_slope_blank_unreachable`. The final pinned original-source CI 41690493736 compiled the actual full dependencies, both odd–odd modules, and all `#print axioms` audits with only the three standard Lean axioms.

Next mathematical question: can the exact odd–odd predecessor wedge be lifted into a uniform backward-invariant obstruction for **all** surviving higher stopping parameters, rather than expanding parameter-wise congruence exclusions? Compare with all recent source-certified Machine C algebra before academic promotion. Keep this intermediate work in `im-results/`.
