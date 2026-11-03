# Agent 9: authentic P1 exponential-cost / affine-wall reduction

**Status 2026-11-03:** All-natural original-source Lean 4.36.0-rc2 success, manual CI [41554472589](https://github.com/FlareZ123/bb6/actions/runs/41554472589), source SHA `05109b5f5a64a1706ae32c3c0b2eb6ef9ad28854`. The theorem uses only `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, new axioms, or source substitutions. **Intermediate result, no P1 / BB(6) decision.**

## Exact genuine-reachability statement

For any q>=1 set P=2^(16q), u=7P-4q-3. Original Agent45 proves that a critical n=16q+2 target is reachable iff either feeder L0=(4u-4,4u+9) or L1=(6u-2,2u+5) is reached. Take an arbitrary genuinely source-defined `OddCone` of one of these two feeders ending at the odd-right hub (b,d) with accumulated cost m. If b>=8, b%4=0, d%2=1, the original `inverseAt b d t=some(k,c)` has even c and k>=2, **and** the original blank-start `BB6.Agent1.Reach (2k-4) (c+4)` holds, then:

- either **m >= 8P**, i.e. the prior odd-inverse cost is at least 8 times an exponential in q;
- or **t=1** and **b=4m+64q+12** on the first feeder L0, respectively **b=4m+64q+16** on the second L1.

This is `BB6.Agent9Dichotomy.authentic_reachable_even_exponential_or_wall` in [DichotomyOriginal.lean](./DichotomyOriginal.lean), using arithmetic lemmas in [DichotomyArithmetic.lean](./DichotomyArithmetic.lean).

An independent, weaker source theorem `BB6.Agent9Cost.reachable_even_terminal_near_full_cost` in [CostOriginal.lean](./CostOriginal.lean) shows that for every r with q<=2^r a reachable even terminal requires `16q<=m+r+4`; the explicit bound is `16q<=m+Nat.log2 q+5`. The pure arithmetic proof is [CostBarrier.lean](./CostBarrier.lean), originally source-checked in CI [41552690195](https://github.com/FlareZ123/bb6/actions/runs/41552690195). Both log-form versions were checked again in 41554472589.

## Arithmetic behind the dichotomy

Source-complete mass conservation yields `b+d+2m=8u+e`, with e=5 for L0 and e=3 for L1. Exact source inversion yields `d+b/2+3=2^t(c+3)` and `2k+c+2t+1=b+d` on an even-c terminal. Genuine reachability gives `2k+8=14*2^j`, with `j<=16q+1`. The parity of odd d and even c forces t>=1; original-source arithmetic bounds t<=16q+4, and 256q<=P.

For **t>=2**, the dyadic equation implies `4(c+3)<=d+b/2+3`. This, the mass identity, the power-index ceiling and the depth bound combine into the strict small-cost contradiction that proves `m>=8P`.

For **t=1**, exact elimination gives

`2k+8 = 28P + b/4 - m -16q - delta`,

where delta=3 for L0, 4 for L1. A reachable power has either `j=16q+1`, whose equality is exactly the stated affine wall, or `j<=16q`, which forces `m>=8P`. Each arithmetic implication and its source bridge is kernel checked.

## Scope, novelty and next gateway

This is stronger than the previously established `m>14q` necessity for q>=13 and `b<=4m+192q+40` narrow-left bound. Both are original-source results by Agent1 and are used as provenance; the dichotomy uses the mass/power equations directly. No exhaustive historical-root decision is claimed, and the external novelty of this intermediate result has not yet been assessed independently.

The **affine-wall case remains open**: it would require excluding any actual `OddCone` node on the feeder-dependent line `b=4m+64q+(12 or 16)`. The exponentially deep alternative remains possible unless a genuine upper bound on inverse cost is established. The separate c=1 exceptional branch and all critical n=14 mod16 require additional reasoning. Synthetic ancestor paths cannot be treated as blank-reachable. Keep this work in `im-results/`, not the academic `results/` index.

Reproduce by dispatching existing manual `.github/workflows/agent1-p1-quarter.yml`, which rebuilds unmodified Agent1, Agent45, Agent47, Agent50 and Agent1Quarter sources before both new modules. The reported `#print axioms` for final bridge is exactly `[propext, Classical.choice, Quot.sound]`.


## Source-verified low-cost wall predecessor rigidity (2026-11-03 01:06 UTC)

The latest original-source kernel run [41557306249](https://github.com/FlareZ123/bb6/actions/runs/41557306249), source revision `b04770dd125f52a9df1f36b354b6a88772c3b89c`, successfully checked additional `OddResetArithmetic.lean` and `OddResetOriginal.lean` against the entire unmodified dependency chain. The final theorem `BB6.Agent9OddReset.low_cost_wall_has_upper_predecessor` reports axioms `[propext, Classical.choice, Quot.sound]`; every arithmetic/reset proof reports only `[propext, Quot.sound]`.

Let `P=2^(16q)`. Any source-defined inverseAt branch with **odd** output right-coordinate `c`, positive nesting depth `t≥1`, and prior cumulative cost `m+t+1<8P`, has new left-coordinate `2k-4≥19P`. When `t≥2`, stronger `2k-4≥29P`. This is exact for every q≥1 and either root feeder, independently of blank-reachability. If such a branch directly lands on the previously derived wall `b=4m'+64q+delta` (delta=12 for L0, 16 for L1), it must have `2m'≥9P`; at depth t≥2 it must have `m'≥7P`.

**Last-upper theorem:** Every wall member `(b,d,m)` of an authentic `OddCone` with `2m<9P` is **not** the initial feeder (both initial feeder coordinates are formally proved outside the wall), and necessarily has a genuine preceding inverseAt edge **at depth exactly t=0**. The predecessor is itself a full source `OddCone` node. The final positive-depth exclusion is unconditional under the low-cost budget and does not rely on enumerating any finite cone. Intermediate `low_cost_wall_last_upper`, `authentic_positive_depth_wall_cost`, `root_not_wall`, and final `low_cost_wall_has_upper_predecessor` are in [OddResetOriginal.lean](./OddResetOriginal.lean).

This is a **necessary predecessor classification**, not a wall exclusion: an arbitrarily long block of depth-zero upper inversions can follow a genuine positive-depth odd reset, and such paths have not been ruled out for every q. Nor is the other branch `m≥8P` excluded. The two original feeder families still have no globally certified nonreachability result. Continue from the last-upper cone, not another short finite residue sieve.
