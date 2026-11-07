# #746: all-index weak-margin elimination of the second-tier low-valuation off-ray arm

**Agent 7, 7 November 2026.** Mathematical intermediate, under source audit, external novelty not assessed. This does **not** settle the blank-start halting status of #746 or the value of BB(6). Original machine table: `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`. The original root in all formal statements is the post-initial genuine configuration `(2,0)`, as in `ResetAncestry.lean`.

## Principal theorem

The [EvenWalkForkDead.lean](EvenWalkForkDead.lean) theorem `GapNumber.offray_tone_low_two_root_dead` establishes the following original-source assertion **uniformly for every** `n>=13`, `j>=0`, `h,w>=0`:

Let `D=deficit n j` and assume
- `n%6 = 4` or `5`;
- `32*D + 64*n + 128 <= 2^n` (weak high-ray margin);
- `9*h + 8*D + 9*n + 7 = 14*2^n`;
- `2*h = 2*2^n + w + (n-2)`;
- `(2*h+5)%27 != 0` and `(2*w+5)%27 != 0`.

Then **no genuine blank-root reset ancestry reaches `(h,0)`**.

The conclusion is *root-sensitive*: it uses the original source `ReachC`, not a guessed inverse-only simulator. No upper bound on `n`, `j`, or the length of the reset ancestry is used. It excludes exactly this specified low-valuation two-tier odd branch; other branches remain.

The prior [Agent 10 high-margin theorem](../agent10-cascade/RayThirdNoRoot.lean) `offray_fork_dead_both_valuation_one` requires `n>=20` and `2048*D+16384*n+16384<=2^n`. The new sufficient condition is substantially weaker. For `n=28,j=16`, the original [EvenChainForkSpecial.lean](EvenChainForkSpecial.lean) explicit low-margin example lies outside the older sufficient margin and inside the new one.

## Proof architecture, with exact dependencies

1. [EvenWalkNoOvershoot.lean](EvenWalkNoOvershoot.lean) proves the elementary all-index exponential separation
   `2*n*(2*n+3)+2*n < 2^(n-13)` for every `n>=25` by induction with an explicit polynomial growth inequality. The proof uses the standard Lean kernel and tactics `omega` and `grind`.

2. Set `p=2^(n-4)`, `M=2^j*(2*n+3)`, and let `B` be the complement of a genuine second-level candidate height `q`: `B+q=8*p`. Original-source equations force
   ```
   81*B+3 = 16*p + 128*M + 169*n,
   2*M + 2*n + 10 <= p.
   ```
   The formal proof of these equations is in [EvenWalkSourceModel.lean](EvenWalkSourceModel.lean). These are exact integer identities, including subtraction guards.

3. In an even inverse walk at fixed scale `k=n-4`, the complementary heights follow
   `B_r = 2^r*B + (2^r-1)*k`. An admissible image height has `3<=B_r<=2*p+1); the impossible gap is `2*p+1<B_r<4*p+3`. The original source [EvenChainGap.lean](EvenChainGap.lean) proves root equivalence along the safe even arm and true-root impossibility in the gap.

4. For `n>=25`, [EvenWalkNoOvershoot.lean](EvenWalkNoOvershoot.lean) proves that one of `B_2,B_3,B_4` enters the gap, and its predecessors stay in the image band. Overshooting the gap after the second or third step would force either
   ```
   0 < 49*2^(n-12) - M < 2*n
   0 < 17*2^(n-13) - M < 2*n
   ```
   respectively. The nonzero difference is a multiple of a power of two greater than `2*n`, contradicting both inequalities. The `near_power_impossible` lemma formally handles arbitrary `j` without brute force.

5. [EvenWalkGapBridge.lean](EvenWalkGapBridge.lean) formalizes the **actual** `evenWalk` arithmetic and explicitly proves every intermediate source band, final gap, and `¬ ReachC (2,0) (q,0)` under the safe modulus-three condition. [EvenWalkSourceModel.lean](EvenWalkSourceModel.lean) derives that safe condition from the original second odd-arm gate `(2*w+5)%27!=0`, its exact `2*w+5=9*d` divisor equation, and `n%6∈{4,5}`.

6. [EvenWalkForkDead.lean](EvenWalkForkDead.lean) invokes the *complete original-source* `offray_fork_root_iff_second_tone` theorem from [RayTwoGateExact.lean](../agent10-cascade/RayTwoGateExact.lean). Every candidate `(q,k,d)` is retained until source dyadic bounds force `k=n-4`. The previous steps then contradict authentic blank-root reachability of `q`, hence of `h`.

7. For `13<=n<25`, [EvenWalkSmall.lean](EvenWalkSmall.lean) proves that the exact `B,M` equations and weak margin have **no integer solution**. It first proves `j<16` from the margin, then uses a `Fin 25 × Fin 16` **kernel-evaluated** `decide` table to eliminate the remaining index pairs, with `#print axioms` to audit standard dependencies. The final root theorem case-splits at `n=25`.

## Verification, limits, and research direction

- Local Lean 4.36.0-rc2 compilation succeeds for all five new modules using exact named interface stubs for unmounted source dependencies; `EvenWalkNoOvershoot.lean` and `EvenWalkSmall.lean` additionally compile standalone without source stubs.
- The complete source CI at [run 42328347614](https://github.com/FlareZ123/bb6/actions/runs/42328347614) passed for the original bound `n>=40` and full original `EvenChainGap` dependency. [run 42328617752](https://github.com/FlareZ123/bb6/actions/runs/42328617752) passed for the original-source `EvenWalkSourceModel.lean`. The current stronger `n>=13` version requires a successful subsequent CI run before being described as fully original-source verified.
- The first [Agent 10 full-source audit run 42328803219](https://github.com/FlareZ123/bb6/actions/runs/42328803219) compiled `EvenWalkNoOvershoot`, `EvenWalkGapBridge`, and `EvenWalkSourceModel` with standard axioms only, then failed to locate `CascadeOddRay.deficit_closed` because the new fork file did not directly import its defining module `OddRayDeep`. This was repaired; the second run is in progress at writing.
- The `im-results` placement reflects that global #746 classification remains unresolved and that mathematical external novelty needs review.

**Still open:** canonical even-ray continuation, deep-valuation `27\mid 2*w+5` and `27\mid 2*h+5` forks, upper-margin regimes outside the weak inequality, all other unresolved machines, an exhaustive BB(6) upper-bound certificate and matching champion witness.

A useful next direction is to prove a generalized *second-tier valuation drain* for `w` divisible by 27, where the original two-gate theorem currently retains an unrestricted `t>=2` source witness. Generalizing the gap calculation from ternary denominator `9` to `3^(t+1)` might cover a further family.
