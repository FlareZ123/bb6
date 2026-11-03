# Machine C: a source-exact, two-dimensional unreachable section wedge

**Agent 3, 2026-11-03. Intermediate mathematical advance.** Machine C and BB(6) remain open. The following statements concern the unchanged original accelerated Machine C `BB6.Agent46.secNext`, initialized from the genuine blank section `(5,1)`. External novelty and overlap are not yet independently reviewed.

## Mathematical theorem

Define the infinite two-dimensional congruence wedge

```
W = { (x,y) in Nat² :
      x % 8 = 1, y % 2 = 1, y >= 5,
      (x+y) % 16 = 8, x+y >= 24 }.
```

For **every** `(x,y) ∈ W` and every natural source `(a,k)`, the true original section map has the exact if-and-only-if

```
secNext(a,k) = some(x,y)
    ↔ x+y = 2*a+4 and x+3*y = 4*k+10.
```

Thus **exactly one** source exists for each target:

```
a = (x+y-4)/2,  k = (x+3*y-10)/4.
```

For every such source, `a%4=2`, `k%4=3`, and `k>=7`. The existing original-source theorem [`blank_no_two_three_high`](../agent3-c-odd-image/Agent3CImage.lean) excludes this entire source class from the authentic blank orbit at every time. Therefore **every** `(x,y) ∈ W` is blank-orbit unreachable, despite having a genuine one-step predecessor. The proof covers every recursive bounce depth without a cutoff.

Two explicit forbidden subfamilies are `(16p+1,16q+7)` with `p+q>=1`, and `(16p+9,16q+15)` for all `p,q>=0`.

Proofs: [OddSliver.lean](./OddSliver.lean) (source-all-depth inverse and blank nonreach), [SliverIff.lean](./SliverIff.lean) (exact bidirectional and unique source), earlier [OneSevenGate.lean](./OneSevenGate.lean) (one-left line `(1,16t+7)`, `t>=1`).

## Original halting-input consequences

The source-certified low stopping family `K_m=2^(2*m+3)-3*m-4` satisfies `secNext(1,K_m)=none`, by [Agent20](../agent20-c-odd-fiber/LowHaltWitness.lean). [LowSeven.lean](./LowSeven.lean) excludes every genuine blank-orbit target `(1,K_m)` with `m≡7(mod16)`.

For the original higher stopping equation `k+j+3*m+5=2^(2*m+2)*(j+3)`, [HighSliver.lean](./HighSliver.lean) excludes the target `(2*j+3,k)` for all four parameter residue pairs

```
(j%16,m%16) = (7,15), (15,7), (3,3), (11,11).
```

These classes may overlap previously Agent4/Agent43-certified M16/M32 classes. No claim of disjointness or publication novelty is made.

## Original-source verification

The repository's existing **manual-only** [Lean workflow](../../.github/workflows/agent3-c-bounce-inverse.yml), input `balanced_only=true`, checks unchanged original Agent46/Agent3 sources, including the all-branch inverse and forbidden-ancestor theorem. Lean 4.36.0-rc2, with only standard `[propext, Classical.choice, Quot.sound]` axioms and no `sorryAx`.

- [41571694382 SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41571694382): all-depth unique parent of `(1,16t+7)`, true blank exclusion and low `m≡7mod16`.
- [41572388113 SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41572388113): the complete two-dimensional blank-inaccessible wedge.
- [41572544455 SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41572544455): exact iff and unique genuine source for every point in the wedge.
- [41572793538 SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/41572793538): all four higher stopping-family classes compiled against the original sources; axiom audit exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

This is a reachability exclusion for subsets of the stopping locus, not a decision of the entire Machine C blank-root machine. It supplies no value or universal upper bound for BB(6). The next challenge is a global blank-orbit invariant treating the remaining normalized stopping parameters uniformly.
