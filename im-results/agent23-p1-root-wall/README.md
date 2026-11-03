# Agent 23: sharp original-source P1 critical-root inverse cost, with the modulo-four terminal wall

**Status:** all major theorems source-connected and Lean 4.36.0-rc2 certified on 2026-11-03. **Intermediate, conditional structural obstruction.** This is *not* a P1 nonhalting result, a BB(6) upper bound, or an exact BB(6) solution. Literature novelty outside this repository has not been independently assessed; keep in im-results.

## The proved necessary condition

Take the original Agent1 accelerated six-state P1 machine
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`,
with exact blank-entry reachability `BB6.Agent1.Reach` beginning at `(2,1)`. Its critical right counter at index `n` is

```
H(n) = 14*2^n-2*n-10.
```

Start an exact **odd-source** inverse cone `OddCone` at the related critical feeder `(H(n)-6,3)=(14*2^n-2*n-16,3)`. After accumulated odd-inversion depth cost `m`, reach a cone node `(b,d)`. Here cost is defined in the original `OddCone` constructors as the sum of `t+1` for every odd-source inverse edge. Suppose `b>=8`, `b%4=0`, `d%2=1`, and an actual original `inverseAt b d t` yields `(k,c)` with `k>=2`, even `c>=2`. Assume its even-right candidate hub `(2*k-4,c+4)` is **genuinely blank-reachable** under the original `Reach`.

For **every n>=14**, our new Lean theorem `BB6.Agent23RootWall.authentic_critical_root_sharp_mod4` proves the disjunction

```
14*2^n <= 6*m+14*n+10
OR
(t=1 AND b=4*(n+m) AND (m+2*n)%4=3).
```

For the central unresolved `n=16*q+14` sector, `n` is even, so the exceptional low-cost wall has **m%4=3**. More generally, non-wall genuine even-right exits have inverse cost at least `ceil((14*2^n-14*n-10)/6)`, which grows asymptotically as `(7/3)*2^n`.

An independent weaker but all-index `n>=4` theorem `authentic_critical_root_sharp_budget` proves the same sharp cost disjunction with just `t=1,b=4*(n+m)` as the low-cost alternative. The all-index original-source `authentic_critical_root_wall_mod4` proves the stronger modulo-four alternative using the coarser threshold `m>=2^n`.

**Boundary:** The result is conditional on an **even source-right counter c>=2** at a leaf of the exact odd-inverse cone. Odd-source continuation, exceptional `c=1` exits, and other terminal cases require separate treatment. No claim of complete universal inverse-cone closure or blank unreachability for residual indices follows. A successful terminal even feeder also requires authentic source reachability, which is not established by satisfying these necessary arithmetic conditions. It may be useful to combine the theorem with complete `GAncestor` branches from Agent1/Agent47 or a future parameter-uniform cone invariant.

## Proof mechanism

The original `odd_cone_mass` supplies the exact mass conservation equation

```
b+d+2*m+2*n+13 = 14*2^n.
```

The original `inverseAt_power` and `inverseAt_exact_mass` for an even source `c` give

```
d+b/2+3 = 2^t*(c+3),
2*k+c+2*t+1 = b+d.
```

Genuine reachability of the even-right source hub invokes the independently existing `even_left_power_shape`, yielding a natural `j` with `2*k+8=14*2^j`. From these exact equations, the arithmetic lemma `critical_root_even_exit_sharp_budget` proves either the full sharp budget inequality, or the identities `t=1, j+1=n, b=4*(n+m)`.

The inequality comes from the full source power/linear constraints. In the `t>=2` case,

```
14*2^n <= 6*m + 8*t + 6*n + 2
          <= 6*m + 14*n + 10
```

because `t<=n+1` is forced by the shifted-right power bound. In the `t=1, j+2<=n` case, the corresponding constraints force `7*2^n <= 2*m+2*n`, which implies the sharp inequality. The only remaining case is the exact affine wall `j+1=n`.

On that wall, an authentic earlier even-phase reset has right counter `r` satisfying

```
r+4*n+2*m+16=14*2^n.
```

If `m` is even, `r%4=0`, and the original `reset_four_power` requires `r+8=14*2^z`, which the sharp-budget `sharp_no_low_wall_reset_power` places strictly between consecutive possible powers. Thus `m` is odd in the low-budget alternative.

If `(m+2*n)%4=1`, then `r%4=2` and `r-6` is divisible by eight. The existing original `reset_mod_four_two_implies_three` gives a genuinely reachable `(r-6,3)=(8*u,3)`. The existing original `reachable_eight_three_requires_power` requires `6*u+8=14*2^z`. This too is forbidden by `sharp_no_low_wall_eight_three_power` for n>=14. Since `m` is odd, the only permitted low-budget cost residue is `(m+2*n)%4=3`.

These are **necessary conditions**; the proof invokes no observed simulation cutoff. The arithmetic helpers have only `[propext, Quot.sound]` as axioms, and the authentic final theorem has only `[propext, Classical.choice, Quot.sound]`.

## Files, source audit and reproducibility

Lean sources in this directory:

- `CriticalRootWallArithmetic.lean`: original coarse exponential-versus-wall derivation, certified.
- `CriticalRootWallOriginal.lean`: original map bridge with precise `Reach`, `OddCone`, `inverseAt`, certified.
- `RootWallOddCostArithmetic.lean` and `CriticalRootWallOddCost.lean`: even inverse-cost exclusion from reset power normal form, certified.
- `RootWallEightThreeArithmetic.lean` and `CriticalRootWallMod4.lean`: coarse modulo-four wall exclusion, certified.
- `RootWallSharpArithmetic.lean` and `RootWallSharpOriginal.lean`: sharp cost inequality, certified.
- `RootWallSharpGaps.lean` and `RootWallSharpMod4.lean`: sharp-budget power gaps and final modulo-four condition, certified.

The existing **manual-only** workflow [`.github/workflows/agent1-p1-quarter.yml`](../../.github/workflows/agent1-p1-quarter.yml) now contains a dedicated **`agent23-root-wall` job**. It compiles every used unmodified original source definition and lemma from `PosEvenForm`, `P1FiniteInverse`, `P1InverseLog`, `MassInverse`, `OddConeMass`, `ResetGate`, `EvenSeed`, `EvenMiss`, `ResetOdd`, `EvenFull`, `EightThree`, `ShiftOdd`, then all new theorem modules; `#print axioms` audits each final theorem.

- Initial original-source CI: [run 41575335116](https://github.com/FlareZ123/bb6/actions/runs/41575335116), `agent23-root-wall` **success**.
- Even-cost elimination: [run 41575615148](https://github.com/FlareZ123/bb6/actions/runs/41575615148), `agent23-root-wall` **success**.
- Modulo-four elimination: [run 41576080014](https://github.com/FlareZ123/bb6/actions/runs/41576080014), `agent23-root-wall` **success**.
- Final sharp-budget theorem: [run 41576609032](https://github.com/FlareZ123/bb6/actions/runs/41576609032), `agent23-root-wall` **success**, job ID `125721462736`. The log explicitly prints standard-axiom audits of both `authentic_critical_root_sharp_budget` and `authentic_critical_root_sharp_mod4`.

**Whole-workflow repair and confirmation (2026-11-03 04:19 UTC):** an already-closed-goal `congr 1` tactic at `L0OneResetBridge.lean:116` caused the existing `source-certify` job to fail. Agent23 removed precisely that tactic in commit `9c72bcdfe264321436f48add0398d8b7b1c7135f`. The next [full manual CI run 41577233075](https://github.com/FlareZ123/bb6/actions/runs/41577233075) completed **successfully in both `source-certify` and `agent23-root-wall` jobs**, independently compiling authentic source and the new theorem. Source semantics and theorem assumptions were unchanged.

Local development also used bundled Lean 4.36.0-rc2. Temporary axiom-based stub modules were employed only for rapid syntax tests while building bridges; they were **never committed** or imported into the repository CI proof. Full source CI imports the actual original `Reach`, `G`, `inverseAt`, `OddCone`, and all original proof dependencies.

## All-upper wall obstruction and the last-positive-reset decomposition

A further independent kernel-checked theorem, `BB6.Agent23RootWall.no_root_upper_wall`, proves **for every n≥14 and every depth L** that

```
14*2^n ≠ 2^L * (4*(n+L)+12) + 2*n+4.
```

An all-depth-zero inverse chain of the exact P1 critical root would necessarily satisfy this identity if it ever landed on the affine wall `b=4*(n+m)`. The proof bounds `L<n`, uses divisibility `2^L ∣ 2*(n+2)` to show `2^L≤2n+4`, and the elementary induction `32*n*n≤2^n` to obtain a strict exponential-versus-polynomial contradiction. It holds uniformly across all n≥14, including the difficult n≡14(mod16) indices.

The stronger source-connected `BB6.Agent23RootWall.critical_wall_requires_positive_inverse` uses the **authentic** Agent1Quarter `OddCone` and `BB6.Agent1UpperTail.odd_cone_last_reset` to show that **every occurrence of the critical affine wall in the entire odd inverse cone** contains an earlier positive-depth inverse step `t≥1`. It returns that step's actual parent in the original inverse grammar and the exact final all-upper tail equation

```
(2*k-4)+12 = 2^L*(4*(n+mp+t+1+L)+12).
```

This tightens the exceptional wall branch of the sharp theorem by requiring a genuine deeper inverse reset in its history. It does not exclude positive-depth reset paths or imply a halting decision.

Verification: original-source Lean 4.36.0-rc2, manual [CI run 41578057833](https://github.com/FlareZ123/bb6/actions/runs/41578057833), dedicated `agent23-root-wall` job **success**, with `#print axioms` returning `[propext, Quot.sound]` on the arithmetic theorem and `[propext, Classical.choice, Quot.sound]` on the full-source bridge. Source files: `RootWallNoInitialUpper.lean` and `CriticalRootWallLastReset.lean`.

## Research follow-ups

1. Develop an all-index bound on accumulated odd-cone inverse cost `m` strong enough to force the low-cost wall. An O(poly(n)) bound would be decisive for the nonwall branch, but is presently unproved. Arbitrarily deep synthetic inverse paths from Agents27/33 warn against unjustified bounded-depth assumptions.
2. Eliminate genuine wall members `b=4*(n+m)` with `(m+2*n)%4=3`; for the residual n14 sector this is `m%4=3`. The related genuine reset has `r%8=2`, leaving an `(r-6,3)` hub with `r-6=4(mod8)`, so the existing eight-multiple theorem no longer suffices.
3. Inspect the exceptional `c=1` and parity-mismatch terminal branches and source-prove that every critical-root ancestry must hit an exhaustive, manageable set of leaf types.
4. Compare with prior Agent9 n2 log-cost dichotomies and Agent1 quarter-index/Agent47 modulo1024 certificates. This theorem is parameter-uniform and targets the n14 sector; shared arithmetic patterns may admit a combined proof.

**Claim boundary:** This is mathematical research progress in a particular open holdout. The exact Busy Beaver function `BB(6)` remains open.
