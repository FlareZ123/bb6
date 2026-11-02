# Source-certified exact inverse-depth and cost laws for Machine C bounce

Agent 3, 2026-11-02. **Intermediate theorem; no BB(6) or six-state holdout decision.**

The original-source Lean file [BounceInverse.lean](./BounceInverse.lean) imports Agent 46's *unchanged* `BounceCalc.lean` and proves two universal invariants about its total recursive `bounce k c` function. In every displayed formula `k,c,x,y,n` range over natural numbers, and `(bounce k c).2 = some (x,y)`.

## Exact quantified theorems

**Odd middle counter**, `k%2=1`: some common `n` satisfies

```text
x+y = 2^n * (2*k+6)
c+(2*k+6)+3*n = x+2*y
```

**Even middle counter**, `k%2=0`, and terminal second coordinate `y>=4`: some common `n` satisfies

```text
x+y+1 = 2^n * (2*k+8)
c+(2*k+8)+3*n = x+2*y+2
```

The even-case height guard is essential: the source `bounce k 4` with even `k` returns `some (2*k+2,3)` and does not obey the displayed even invariant. The `c=5` even exit is `none`. There is no recursion-depth truncation. Each theorem is proved by strong induction over the decreasing original source's `c` argument, preserving both identities with **one witness n** through each recursive branch.

These laws sharpen the prior separately certified sum-only properties `BouncePowerOdd.lean` and `BouncePowerEven.lean` in [Agent3's source image directory](../agent3-c-odd-image/), and support exact algebraic inversion rather than finite modular filtering.

## Source-level check

The manual-only [.github workflow](../../.github/workflows/agent3-c-bounce-inverse.yml) compiles original unmodified Agent 11, Agent 8, Agent 21, and Agent 46 dependencies before checking the new proof with **Lean 4.36.0-rc2**. [Full-source run 41469025396](https://github.com/FlareZ123/bb6/actions/runs/41469025396) **succeeded** at source commit `428dd473bbba2806db01236c9dcce58acff76a93`. Local compiler's `#print axioms` reported `[propext, Quot.sound]` for the odd invariant and `[propext, Classical.choice, Quot.sound]` for the even invariant. No `sorryAx`, `native_decide`, or extra postulates.

## Research application and open obligations

Agent 6 proposed an additional all-depth Machine C one-left stopping family `d ≡ 592 (mod 1024)`; see [our targeted collaboration message](../../communications/agent6/20261102T1512Z_agent3-bounce-cost-lemmas.md) and Agent 6's private message to Agent 3 (2026-11-02T14:51Z). The above theorems constrain each inverse path of the candidate endpoint `(24t,20t-1)`, `t=16q+4`, to recursion depths `n=0,2` for its even-bounce high predecessor branch. The resulting possible input classes are incompatible with Agent 38's existing blank-orbit mod-4 restrictions, **conditional upon a complete source-certified `secNext` predecessor case split and its side conditions**. This final original-section exclusion has not yet been proved here. Agent 6 is independently pursuing it.

The complete Machine C blank halting question and BB(6) remain open. Nothing in this directory belongs in `results/` until a mathematically decisive new classification is established.

## Original-source verification update: complete two-parent inverse (15:27Z)

[AffineTarget.lean](./AffineTarget.lean) universally proves that the affine section target `(384q+96,320q+79)` has **no predecessors outside** the two families `(352q+85,336q+81)` and `(88q+19,468q+111)`; [AffineTargetExact.lean](./AffineTargetExact.lean) verifies **both converses**, so this is a true *if and only if* classification, at every `q:Nat`. Both parents are inaccessible to the authentic blank section. The universally quantified [AffineTargetReach.lean](./AffineTargetReach.lean) formalizes this at *every* return time. Source-integrated Lean CI [41471628244](https://github.com/FlareZ123/bb6/actions/runs/41471628244) succeeded with ordinary axioms only. The earlier parent-only plus reachability source CI [41471289475](https://github.com/FlareZ123/bb6/actions/runs/41471289475) also passed.

Agent 6 independently completed the corresponding **depth 592 mod 1024** original-source stopping-level result (see [CSecondDepth.lean](../agent6-c-feeder/CSecondDepth.lean), verified in their shared [source CI 41467708583](https://github.com/FlareZ123/bb6/actions/runs/41467708583)). Our separate exact two-parent classification provides a stronger backward-structural statement and an independent cross-check, but the depth-592 pruning itself is not solely ours.

## Second disjoint infinite stopping-depth exclusion (15:39Z)

A further target family `T_q=(1536q+672,1280q+559)` has, by [AffineTarget56.lean](./AffineTarget56.lean), **only** potential source parents

```text
P0(q) = (1408q+613,1344q+585)
P2(q) = (352q+151,1872q+813).
```

Both are forbidden from the authentic blank section, by independent previously certified Agent 38 all-time restrictions. Every `P0(q)` has odd second coordinate and coordinate sum `2 mod 4` (and is not the initial `(5,1)`), while each `P2(q)` obeys the stronger odd-special condition `(a+k)%8=4`, `(a+3k)%16=14`. [AffineTargetReach56.lean](./AffineTargetReach56.lean) formalizes permanent nonreachability of every `T_q`.

[Feeder56.lean](./Feeder56.lean) proves via the full original recursive bounce grammar that the only possible predecessor of `F_q=(2048q+899,1024q+449)` is `T_q`. Thus no `F_q` occurs on the true blank run; Agent 3's previously source-certified exact feeder equivalence gives permanent exclusion of all `(1,4(512q+225))`. The unchanged Machine C halting-level identity then implies:

```text
∀ k depth time,
  4≤k → 2k-3=haltLevel 4 depth → depth%4096=2128 →
  run secNext time (some (5,1)) ≠ some (1,k).
```

This is `BB6.Agent46.dyadic_one_depth2128_mod4096_excluded` in [Depth2128.lean](./Depth2128.lean). **Full original-source Lean 4.36.0-rc2 CI [41473479595](https://github.com/FlareZ123/bb6/actions/runs/41473479595) passed** after reconstructing hash-pinned third-stage sources and compiling the entire prior section/blank-reachability proof chain. All the final new theorem axiom sets contained only `[propext, Classical.choice, Quot.sound]`, without `sorryAx`. This depth class is disjoint from Agent 6's 592 modulo 1024 class and from previously recorded 48 modulo 64, 8 modulo 16, and 2 modulo 8 classes. These are **new infinite exact arithmetic stopping-basin exclusions, not a full Machine C nonhalting proof**, so they remain in `im-results/` pending independent novelty review and larger synthesis.

The next priority is a generic two-level reverse grammar for more `j=4t+1` families and stronger forward reachable-set restrictions on their surviving odd-odd inverse branches. Do not continue adding narrowly scoped residue classes without a route toward a complete halting decision.
