# Machine C: exact affine-depth barriers for blank-origin stopping gates

Agent 11, 2026-11-02. **Intermediate mathematical research, original-source CI pending for the newest theorems.** This work does not settle Machine C's halting status, BB(6), or the universal upper-bound task. Preserve in `im-results/` pending reproducible full-chain verification and independent novelty review.

## Principal result: unbounded-depth 2-adic predecessor obstruction

The unmodified original Machine C first-return section map is `BB6.Agent46.secNext`, with blank-origin initial pair `(5,1)`. Write `CReach(a,k)` for exact eventual reachability of pair `(a,k)`, and `oddDepth(k)` for the number of forced affine predecessors when the first counter is 3 mod 4, as in Agent15's source-certified `AffineParityDepth.lean`.

**Theorem (source-composition candidate, `AffineDepthM8.lean`):** for arbitrary naturals a,k satisfying
```text
a%4 = 3,
(a+2*k)%8 = 7,
oddDepth(k)%2 = 0,
k+2 = 2^oddDepth(k) * (8*q+6)   for some q,
```
we have `¬CReach(a,k)`. This is a whole two-dimensional, variable-depth reachable-set obstruction, quantified over unbounded counters and depths. Proof: let `(A,K)=affineNormalize(a,k)`, the **exact** blank-reachability-preserving forced inverse from Agent15's `ReachAffine.lean` and `AffineNormalize.lean`. Its formally derived invariants are `A+2K+4*oddDepth(k)=a+2k` and `2^oddDepth(k)*(K+2)=k+2`. The assumptions imply `(A%8,K%8)=(7,4)`, contradicting the source-certified full-orbit quotient theorem `blank_no_m8_cylinder`. The proof is independent of simulated blank trajectories or any fixed recursion-depth search limit.

**Consequence (`DeepLowGate.lean`):** for every odd positive u, if `d=oddDepth(21u−3)` is even and `21u−1=2^d(8q+6)` for some q, then `¬CReach(1,32u+4)`. Agent3's exact three-section `low_gate_all_parents_iff` forces every such low gate to derive from the state `(22u−3,21u−3)` because the odd u excludes every higher even-bounce inverse depth. Its first counter is 3 mod4, weighted sum 7 mod8, and the general invariant above eliminates it.

**Unbounded hierarchy (`DeepFamily.lean`):** the source expression `oddDepth` has the universally quantified exact formula
```text
oddDepth(2^(2r+1)*(4q+3)−2) = 2r
```
for every r,q. Therefore for any r,q,u with
```text
21u−1 = 2^(2r+1)*(4q+3)
```
the genuine blank section never reaches `(1,32u+4)`. Its proof is a complete induction over r and two exact inverse steps at each induction successor. There is no bound on r. For each fixed r the Diophantine condition has infinitely many positive solutions: choose q satisfying `2^(2r+1)*(4q+3)≡−1 (mod21)` and increase q by 21. Since 21 is odd and coprime to 2, and multiplication by 4 is invertible modulo21, the condition has exactly one class of q modulo21. It determines a whole infinite nonreachability family at arbitrary forced-inverse depths.

## Explicit machine-halting parameters removed

The original Agent15 first halting family has the exact equation `k+3m+4=2^(2m+3)` and requires reaching `(1,k)`. Repeated use of Agent3's complete inverse and the above quotient/normalizer forbids the following entire index congruences:

| First-halt index | First-family candidate gate | Source theorem | Status |
|---|---|---|---|
| `m%256=136` | `k%256=100`, `t=(k−4)/16%16=6` | `LowGate6.first_halt_m136_mod256_unreachable` | Lean source job 41519952402 pending |
| `m%1024=456` | `k%1024=676`, `t%64=42` | `AffineDepthM8.first_halt_m456_mod1024_unreachable` | Lean source job 41522387396 pending |

These two classes are **disjoint**: the former is `m%256=136`, the latter `m%256=200`, and both lie in `m%16=8`, a sector that passed Agent15's earlier `affineQuotientExcluded` filter. Passing that filter never implied reachability. The general Diophantine hierarchy subsumes these as r=0 and r=1. It yields additional all-time low-gate exclusions for arbitrarily large r, without requiring a finite residue-class enumeration.

## Formalization files and provenance

- [`AffineDepthM8.lean`](./AffineDepthM8.lean): all-natural affine normalization exclusion; explicit two-level residue witness; `t%64=42` and first-family `m%1024=456`.
- [`DeepLowGate.lean`](./DeepLowGate.lean): uniform all-depth odd-u gate obstruction.
- [`DeepFamily.lean`](./DeepFamily.lean): exact unbounded `oddDepth` induction and Diophantine hierarchy.
- [`LowGate6.lean`](./LowGate6.lean): t%16=6 and first-family m%256=136.
- Original source dependencies: Agent3 [`EvenTargetOrbit.lean`](../agent3-c-bounce-inverse/EvenTargetOrbit.lean), source CI [41513332787](https://github.com/FlareZ123/bb6/actions/runs/41513332787); Agent15 [`AffineParityDepth.lean`](../agent15-c-halting/AffineParityDepth.lean) and [`M8M16Composition.lean`](../agent15-c-halting/M8M16Composition.lean); Agent41/43 quotient [`Mod8SevenFour.lean`](../agent41-c-quotient512/Mod8SevenFour.lean) with original CLine source.
- Two manual **original-source** CI invocations: [41519952402](https://github.com/FlareZ123/bb6/actions/runs/41519952402) (first low-gate), [41522387396](https://github.com/FlareZ123/bb6/actions/runs/41522387396) (full all-depth hierarchy). The same existing `.github/workflows/agent15-c-halting.yml` compiles original imported source and prints every new theorem's axiom set. These jobs were still in progress at the time of this update. In the local environment Lean 4.36.0-rc2 accepted all exact proof bodies against matching theorem signatures, with no sorry. That preliminary check is **not** a substitute for full-source compilation.

## Earlier independent verification, explicitly credited as prior art

[`First24.lean`](./First24.lean) shows all first-family `m%32=24` unreachable by combining Agent15's exact single-affine predecessor with Agent38's blank `odd_special` exclusion. Complete original-source Lean CI [41518668629](https://github.com/FlareZ123/bb6/actions/runs/41518668629) passed, axioms exactly `[propext, Classical.choice, Quot.sound]`. **Agent3 had already proved a stronger theorem `low_gate_odd_t_excluded`** encompassing this residue. Consequently `First24` is an independent sanity check only and carries **no claim of mathematical novelty**.

## Open problem

The above barriers are one-sided exclusions. The remaining uncountable-in-computation infinite families of halting input parameters are not all eliminated, and Machine C remains undecided. A stronger global forward invariant or an infinite inverse argument covering the residual halting family would still be necessary for a whole-machine nonhalting theorem. The overall exact BB(6) objective further requires resolving all other holdout machines and a complete universal proof of the six-state enumeration bound.
