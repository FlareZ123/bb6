# Strict-growth certificates for two BB(6) holdout accelerations

**Status: intermediate results.** These theorems do not prove that either original machine halts or runs forever. They are stored in `im-results/` accordingly.

## Source transitions

The transitions in [RankCertificate.lean](./RankCertificate.lean) reproduce the `next` definitions in two independently established, Lean-certified acceleration modules from Google DeepMind's [Cryptids](https://github.com/google-deepmind/cryptids) repository:

1. **Machine A** `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, originally nicknamed *The Sheep Machine*. [Upstream Lean module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean). Upstream initial counter state `P(0,2)`; halting counter states have `m=1`; `nextA` is its transition function after replacing the constructor `P` by a pair.

2. **Machine B** `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. [Upstream Lean module](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean). Upstream initial counter state `A(3,0,0)`; halting counter states have `a=b=0`; `nextB` is its transition function after replacing constructor `A` by a triple.

The upstream files contain the formal proofs `is_valid_acceleration` and `isHalt_iff_acceleration`. This standalone file proves properties of exact copies of the published accelerated maps. It is not imported directly into Cryptids, so the correspondence is established by inspection, rather than by an additional kernel-checked bridge.

## New intermediate observations

For every `nextA s = some s'`, the integer potential `m+k` strictly increases. For every `nextB s = some s'`, the potential `a+b+c` strictly increases. Lean proves these universally for all natural counter inputs, rather than for an experimental prefix.

The generic theorem `rank_growth` proves that a surviving `n`-step accelerated trajectory increases its initial potential by **at least `n`**. Consequently:

- The Sheep Machine has `m+k ≥ n+2` after any `n` surviving macro steps, starting at `P(0,2)`.
- Machine B has `a+b+c ≥ n+3` after any `n` surviving macro steps, starting at `A(3,0,0)`.
- No surviving accelerated path can revisit an earlier counter state. **Conditionally**, if the corresponding original TM never halts, its encoded macro-configuration footprint is unbounded. The Sheep encoding contains precisely `m+k+1` one-bits; the second contains `a+b+2(c+1)` one-bits.

These are escape-to-infinity certificates that rule out finite macro-state cycles. They leave open whether the paths enter their designated halting states.

## Verification

Run Lean **4.36.0-rc2** directly on `RankCertificate.lean`; it imports only `Lean.Elab.Tactic.Omega`, with no Mathlib or upstream Cryptids dependency. The local compilation exited with status 0.

Follow-up work: connect these certificates to the original Cryptids modules through a Lean import, and investigate whether stronger modular/inequality invariants can exclude the halting sets. A rank potential alone does not do so.


## Third machine: weighted potential and certified sweep shortcut

**Machine C** `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, from [Cryptids' formal acceleration](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean), starts at `B(5,0,1)` and halts its accelerated dynamics when `c=2`. Its accelerated state is `(a,k,c)`.

[RankC.lean](./RankC.lean) kernel-checks the weighted integer `R = a + 2*k + c`: on every surviving accelerated transition, either `R` increases, or `R` is unchanged and the first counter `a` decreases. The natural-valued **quadratic potential** `E = R*R + (R-a)` consequently increases strictly at every surviving transition. Starting from `B(5,0,1)`, `E=37`, so any surviving `n`-step macro run satisfies the formally proved bound **`37 + n ≤ R*(R+1)`**. This is a uniform superlinear-potential lower bound on the rank growth and rules out recurrent macro configurations, conditionally on the run continuing.

[Sweep.lean](./Sweep.lean) independently certifies the exact shortcut: for any `q≤a` and `q+3≤c`, `q` consecutive high-counter sweep steps can be replaced by `(a,k,c) → (a-q,k+q,c-q)`. A simulator can safely choose `q=min(a,c-3)` when `a>0,c≥4`. The shortcut reduces billions of affine decrement transitions to single jumps; it was compiled locally using Lean 4.36.0-rc2 with imports `RankCertificate` and `RankC` (each compiled to `.olean` first).

Neither certificate excludes the designated halting state `c=2`. The correspondence between standalone `nextC` and the upstream published `next` is verified by comparing their definitions, and would benefit from an explicit kernel-checked cross-module bridge.


## Certified critical guard

[Critical.lean](./Critical.lean) verifies all predecessors of the halting layer `c=2`: `(0,0,0)` and `(0,2j,5)`. [CriticalReach.lean](./CriticalReach.lean) proves that the initial state `(5,0,1)` cannot reach `(0,0,0)`, using monotonicity of `R=a+2k+c`. Consequently, its theorem `nextC_stops_iff_critical` certifies:

```lean
theorem nextC_stops_iff_critical :
    CollatzStops nextC (5,0,1) ↔
      ∃ n j, runSteps nextC n (5,0,1) = some (0,2*j,5)
```

[CriticalBounds.lean](./CriticalBounds.lean) further proves `j>0` at any reachable critical state and `37+n ≤ (4*j+5)*(4*j+6)` for a critical encounter after `n` surviving macro steps. **These are exact properties of the accelerated map, not a nonhalting proof.**

## Reproducible computational experiment

[AcceleratedC.cpp](./AcceleratedC.cpp) implements the same transitions and the formally checked sweep shortcut. It uses unsigned 128-bit macro-step counts and a guard against counter overflow. The independently implemented Python scalar map was compared against unaccelerated C++ at 100,000 and 1,000,000 steps; plain and skipping C++ simulators matched at 1 billion steps, and 64-bit and 128-bit shortcut variants matched at `10^18` steps.

At exactly `10^18` surviving accelerated steps, state `(3275195632,829068763,358117677)` was observed. At exactly `10^20` steps the state was `(3468056923,20301726861,8843523918)`. No halt was observed in either simulation. The `10^20` simulation used 30,237,230,344 unskipped event transitions and 15,118,567,736 exact sweep jumps. It encountered `(a,c)=(0,5)` once, with odd `k=1053` at step 156,095, and never encountered a reachable halting precursor. This is finite empirical evidence. The original Turing machine's halting status remains unresolved.

## 2026-11-02: optimal triangular-width lexicographic potential (source certified)

Agent 8's earlier potential `R²+R-a` gives `37+n ≤ (4j+5)(4j+6)` for a reachable old halt precursor `(0,2j,5)`. The strictly tighter potential
`P(R,a)=R(R+1)+2(R-a)`, where `R=a+2k+c`, increases **by at least two** along every surviving transition. This uses the original exact lexicographic progress proof: if R is unchanged then a strictly decreases, and an increase of R by one more than compensates even for the worst possible a reset.

Hence every exact n-step surviving counter path from `(5,0,1)` to `(0,2j,5)` satisfies
```
44 + 2*n <= (4*j+5)*(4*j+8).
```
The coefficient of the leading `j²` on the right is 16 rather than the original 16 with n coefficient 1, giving approximately a factor-two stronger n restriction for large j. This bound still does not exclude any unbounded gateway family or determine halting, and belongs in `im-results/`.

The exact files are `PotentialCore.lean`, `PotentialC.lean` and `PotentialBridge.lean`. The last file proves by Lean definitional equality that the copied `BB6Rank.nextC` is precisely the **original unmodified** `BB6CLine.nextC`, and transfers reachability over a finite step count to the actual published source. This is not merely an inspected correspondence. Manual [source-level CI run 41417851833](https://github.com/FlareZ123/bb6/actions/runs/41417851833) compiled the full original `RankCertificate`, `RankC`, `CLine` modules plus the three new files with Lean 4.36.0-rc2. The terminal axiom audit is exactly `[propext, Quot.sound]` for `source_critical_time_bound`, and `[Quot.sound]` for `source_nextC_eq`; there is no `sorryAx`. The manual-only workflow is `.github/workflows/agent8-c-potential.yml`.
