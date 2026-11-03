# Agent 6: BB(6) #429 harmonic-gate and corridor transfer programme

**Status (2026-11-03): substantive intermediate mathematics, locally Lean-kernel checked. No original blank-root halting decision, BB(6) exact value or universal BB(6) bound.** The full original DeepMind/Cryptids source-import chain remains unverified in GitHub CI because Actions jobs currently fail before executing.

## Machine and mathematical semantics

The exact rooted RLE is `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`, the Cryptids #429 of the dated hard list. The original pinned [Cryptids source](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) gives an exact primitive-TM acceleration to `J(u,w)`, starting at `J(0,0)` after 35 raw primitive steps, with a halting action on `w+1=2u`. The local model is `BB429.next : Nat × Nat → Option (Nat × Nat)` and `BB429.run` as defined in [Agent 5's source transcription](../agent5-429-rank/BB429Rank.lean); its exact transition branch order and truncating natural arithmetic are crucial.

Write `U(k)=3(2^k-1)`, `V(l)=14*2^l-3`. The first-branch run from root 0 has `rayDemand(k)+3k=2U(k)`, and from root 11 has `demandV(l)+3l+22=2V(l)`. Earlier conditional affine ladders are proved in [ReturnLadder.lean](ReturnLadder.lean).

## New quantified mathematical conclusions

1. **Infinite escape ray** ([EscapeRay.lean](EscapeRay.lean)): for every `u≥17`, `u%4=1`, `run 4 (u,u+8) = some (u+8,u+16)`; for every `n`, `run n (u,u+8) ≠ none`. The induction has exact all-four-state macro semantics, not a finite observed trace. A real proven entry to the ray would transfer all-time nonhalting, but no entry from the genuine blank `(0,0)` is known.
2. **Two infinite synthetic root families** ([EscapeRoot.lean](EscapeRoot.lean)): `rootU(k)+3k+1=9*2^k` for `k≥3`, `rootV(k)+3k+23=42*2^k` for `k≥1`. Starting from `(0,rootU(k))` or `(11,rootV(k))` enters the escape ray after exactly `k` accelerated steps and survives forever. These starting points are **not** the genuine blank-entry counter state.
3. **Complete U-even corridor transfer** ([ExitTransfer.lean](ExitTransfer.lean), [CorridorExceptions.lean](CorridorExceptions.lean), [WholeCorridor.lean](WholeCorridor.lean)): if `k≥6`, `k%4=2`, `w%4=0`, `w+4≤2U(k)`, then at some finite time the orbit reaches `(V(k-2),y)` with `y%4=2`, `y+4≤2V(k-2)`. The proof takes the maximal `U` ladder using `Nat.div` and `Nat.mod`, then handles *all* three possible boundary cases with exact times `2k+2`, `3k+3`, `4k+6` (each conditionally on the boundary residue). There is no unverified omitted residue.
4. **Complete V-even corridor transfer** ([VExitTransfer.lean](VExitTransfer.lean), [VWholeCorridor.lean](VWholeCorridor.lean)): if `l≥4`, `l%4=0`, `w%4=2`, `w+4≤2V(l)`, then at some finite time the orbit reaches `(V(l+1),z)` with `z%4=1`. Regular boundary `r≤3l+12` uses exactly `l+2` macro steps; the remaining `r=3l+16` uses exactly `3l+8`, visiting a root-zero U-ray. This is sector transport, not indefinite nonhalting.
5. **A fifth conditional cross-ray ladder** ([CrossRayReturn.lean](CrossRayReturn.lean)): for `l≥4`, `l%4=0`, `w%4=1`, and guard `3w+6V(l+1)+9(l+3)+36≤8U(l+3)`, the exact return is `run (2l+8) (V(l+1),w)=some (V(l+1),w+6l+60)`. A parameter-uniform induction proves arbitrarily many *guarded finite repetitions* `n`, with the final guard; it does **not** assert unlimited repetitions for fixed `l`.
6. **Real blank-origin accelerated checkpoints, proved by composing these parametric theorems:** `run 79 (0,0)=some (U(6),48)`, `run 156 (0,0)=some (U(6),356)`, `run 170 (0,0)=some (V(4),366)`, `run 186 (0,0)=some (V(5),17)` ([VWholeCorridor.rooted_to_V5_17](VWholeCorridor.lean)), and `run 202 (0,0)=some (V(5),101)` ([CrossRayReturn.rooted_to_V5_101](CrossRayReturn.lean)). These finite macro checkpoints do not improve any known world record or the global BB(6) lower bound.


## New two-stage odd-counter grammar (2026-11-03 19:37 UTC)

The following expansions are source-mirror kernel checked together with all
dependencies in [manual CI run 41704791733](https://github.com/FlareZ123/bb6/actions/runs/41704791733)
(Lean 4.36.0-rc2, standalone-proof job succeeded, `#print axioms` on principal
lemmas contains only standard Lean axioms). The separate original Cryptids
native-source build is still unverified.

1. **U odd boundary trichotomy and missing seam**:
   [OddBoundary.lean](OddBoundary.lean) proves exact two-step formulas
   for the return, `3w=2u+19` seam and strict overflow.
   Every ray `U(k)` is divisible by three, so that seam is impossible
   for all ray states; the remaining two cases are exhaustive under the
   explicit guard `w+7≤2U(k)`.
2. **Complete admissible V-odd cross-ray split**:
   [CrossRayOverflow.lean](CrossRayOverflow.lean) establishes, uniformly
   for `l≥4`, `l%4=0`, `w%4=1`,
   `3w≤2V(l+1)+1`, that the previously proven return guard gives the
   `2l+8` affine V return, while failure gives a precise `l+7`-step
   overflow `(2U-z+18,3z-2U-22)`,
   `z=2V+w+17-rayDemand(l+3)`. A ray budget
   `8V+9(l+3)+73≤12U` discharges all cap assumptions.
3. **New U-odd bounce sector**: [OddUBounce.lean](OddUBounce.lean)
   proves `run(k+4)(U(k),w)=(U(k),w+3k+31)` when `k%4=3`,
   `w%4=3` and the explicit overflow/return guards hold.
   The arbitrary finite `n` ladder is also proved.
4. **Second-stage modulo-eleven exclusion and odd V-one bounce**:
   [OddCascade.lean](OddCascade.lean) proves
   `U(2n+1)%11∈{3,10,5,7,4}`, excluding both
   possible second-stage U-ray seams
   `11w=10U(k)+107` or `11w=10U(k)+111`.
   It completes the two-level U split under stated caps,
   with strict four-step overflow
   `run 4 (U(k),w)=some ((6U(k)+68)-5w,11w-10U(k)-112)`.
   A further affine sector at `V(k)`, `k%4=1, w%4=1`,
   gives `run (k+4) (V(k),w)=some(V(k),w+3k+41)`,
   with a finite `n` ladder.
5. **More genuine blank-seed finite milestones**: compositions yield
   `run 213 (0,0)=some(513,17)`,
   `run 222 (0,0)=some(U(7),319)`,
   `run 233 (0,0)=some(U(7),371)`,
   `run 237 (0,0)=some(499,159)`,
   `run 244 (0,0)=some(V(5),313)`, and
   `run 262 (0,0)=some(V(5),425)`.
   All times count accelerated high-level map applications, not primitive
   Turing-machine steps. None proves an infinite orbit.

**Evidence classification:** These are new results within this shared
repository as far as this invocation can determine. Independent novelty
relative to wider published mathematics has not been established. Every
new statement is conditional or finite, and all new work remains in
`im-results/`. The original-source bridge is a separate open obligation.

## Reproduction and evidence quality

- **Lean:** Local Lean `4.36.0-rc2`, original Agent 5 source-equivalent arithmetic `next/run` and preserved Agent 6 helper statement definitions, checked all new modules. `#print axioms` on the principal transfer theorems and rooted witnesses produced only standard kernel foundational axioms `propext`, `Quot.sound` (and `Classical.choice` where used), no `sorryAx` or `native_decide`. The **unchanged full original modules** have *not* been compiled with the new files in a successful CI/source environment, so this evidence is accurately described as **local source-mirror kernel checked; original-source CI pending**.
- **Independent BigInt SFT:** [BB429ExitSFT.cjs](BB429ExitSFT.cjs) checks 920 boundary endpoint cases, including 23 samples of each exceptional type, across `k=6,10,...,94`; it checks all exact endpoint states/times, V-even guard, synthetic escape rays and two rooted-family samples, plus real blank-entry macro checkpoints 79,156,170. This is finite crosscheck, not universal proof.
- **Further bounded observation:** A deterministic `30,000,000`-step accelerated simulation from `(0,0)` reached `(893,110318220)` without a macro halt or any visit to the escape ray. Published upstream research reports much longer simulation. No finite observed prefix proves nonhalting.
- **External novelty:** Not independently assessed. The original Cryptids accelerated map and Agent 5/previous Agent 6 ladders are prior art; new results refine the local transition grammar. Keep these provisional intermediate contributions under `im-results/` and request independent source and novelty review before publishing.

## Open proof obligations

The true blank trajectory has not been shown to reach the escape ray; neither has an all-time blank-seed invariant excluded the halting line. The V-odd phase beyond the newly proved finite return and overflow cascades remains structurally open. Rebuild against the *unchanged original* Agent 5/Agent 6 Lean module imports, then test native Cryptids `highLevelNext` bridge in a source-matched successful CI job once GitHub Actions has recovered. Avoid repeating long uninformative traces and routine modular residue sweeps.

[Research issue](../../research/issues/R-20261103T1117Z-agent6-harmonic.md) | [Main mathematical frontier](../../results/README.md)
