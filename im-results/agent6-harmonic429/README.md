# Agent 6: BB(6) #429 harmonic-gate and corridor transfer programme

## 2026-11-04: original-source verification repaired, new infinite modular gates

**Native pinned source verification is now successful:** manual [CI 41765557427](https://github.com/FlareZ123/bb6/actions/runs/41765557427), source job 126362985268, built the unchanged original DeepMind Cryptids `c86f15861709b76042998c5211c7b2f83991621b` accelerator under pinned Lean 4.35.0-rc4, then compiled the original checked-in Agent5/Agent6 local module chain and `SourceLadder.lean` with the actual `highLevelNext`. This includes `source_step_eq`, `source_run_eq` and source-connected return/finite blank checkpoint theorems with standard Lean axioms only. The previous CI blocker was a wrong targeted Mathlib-cache path. Changing the manually dispatched job to the established `lake exe cache get` workflow, without changing upstream mathematics, repaired it. The separate [CI 41766575228](https://github.com/FlareZ123/bb6/actions/runs/41766575228) standalone job also compiled the new `BB429Mod8.lean` against unchanged checked-in `BB429Rank.lean`.

**New all-time accelerated blank-orbit modular restriction.** [BB429Mod8.lean](BB429Mod8.lean) proves `Allowed (u,w)` is preserved by every successful exact `BB429.next` from genuine accelerated start `(0,0)`. Its modular predicate admits 17 of the 32 possible pairs `(u%8,w%4)`. The universal theorem `blank_halting_u_residue` requires every actual accelerated halting configuration to satisfy `u%8∈{1,3,5}`, excluding five u classes mod8. [BB429Extra11.lean](BB429Extra11.lean) sharpens the modular requirement to `u%16∈{1,3,5,9,13}`: for every allowed predecessor, a successor with `u%16=11` cannot have `w%4=1`, while every halt has `w+1=2u`. This is a derived necessary condition with unconditional all-natural quantified hypotheses; it does not prove Machine #429 nonhalting.

[SourceMod16.lean](SourceMod16.lean) transports that mod16 result to the unchanged Cryptids source accelerator using `SourceLadder.source_step_eq` and `source_run_eq`; at this documentation checkpoint, **the new source-native SourceMod16 module remains under the manual audit run** and must not be called native-source-certified before a successful job. The standalone BB429Extra11 Lean certificate uses standard foundation axioms, no `sorryAx` or `native_decide`; definitive GitHub CI provenance should be added after inspection. More limited finite-modulus BFS suggestions are computational proposals and not proven all-time results.

These are **intermediate internal advances**, not a six-state universal census or an exact BB(6) value. Keep them under `im-results/`; external novelty remains unevaluated. The next mathematical step is to rule out a surviving genuine halt gate or produce a real blank-root halting witness rather than repeatedly increasing moduli.



**Status update (2026-11-04): substantive intermediate mathematics, native original-source bridge successfully checked in CI 41765557427. No blank-root halting decision, BB(6) exact value or universal bound.** The historical 2026-11-03 report below predates this source verification.

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


## Further source-shaped odd-V phase (2026-11-03 19:55 UTC)

A complete 4-module extension of the conditional return grammar has now
passed full standalone Lean 4.36.0-rc2 dependency-chain CI:
[run 41707490415](https://github.com/FlareZ123/bb6/actions/runs/41707490415).
The original-source native bridge is being separately audited.

- [OddVSecondary.lean](OddVSecondary.lean) gives the exact second odd-V
  overflow \`run 4 (V_k,w)=((6V_k+48)-5w,11w-10V_k-72)\` under its
  two-step cap and overflow conditions. A further odd-odd reset and
  demand guard returns to the U_(k+2) ray after \`k+8\` macro moves.
  Rooted witness: \`run 275 (0,0)=(U_7,615)\`.
- [OddVHigh.lean](OddVHigh.lean) proves a third V-one odd affine
  sector: for \`k%4=1,w%4=1\`, \`w+7≤2V_k\`,
  \`6V_k+33≤5w\`, \`9w≤14V_k+75\`,
  the precise return is
  \`run(k+4)(V_k,w)=(V_k,w+3k+33)\`.
  Also provides an arbitrary finite bounded ladder, rooted
  \`run 286(0,0)=(V_5,553)\` and a fourfold transfer to
  \`run 322(0,0)=(V_5,745)\`.
- [OddVThirdOverflow.lean](OddVThirdOverflow.lean) derives the
  third-stage root-zero transition
  \`run 6 (V_k,w)=(0,2V_k+w+33)\` when
  \`14V_k+82≤9w\`, \`35w≤58V_k+345\`
  and the preliminary cap/overflow guards hold. With the exact U ray
  demand, \`run(k+9)(V_k,w)\` reaches U_(k+3).
  Real blank-derived witness: \`run 336(0,0)=(U_8,162)\`.
- [OddVHighReturn.lean](OddVHighReturn.lean) closes the latter
  excursion by proving the **new complete conditional high-V return**:
  \`run (2k+10) (V_k,w)=(V_k,w+6k+62)\`
  when the explicit gates above, \`k%4=w%4=1\`, and
  \`rayDemand(k+3)≤2V_k+w+33\` hold.
  Its uniform margin
  \`4V_k+30+3(k+3)≤4U_(k+3)\` guarantees the
  U-to-V reset cap for all k≥1. The theorem proves the actual
  blank-origin orbit satisfies \`run 342 (0,0)=(V_5,837)\`.

These structural results are conditional and finite. None gives a
nonhalting invariant for the original \`J(0,0)\` orbit or a universal
six-state maximum. External novelty is not established; keep under
\`im-results/\` pending outside review. The original-source bridge
requires an independent successful native-source CI build before
source-connected formal verification may be claimed.

## Reproduction and evidence quality

- **Lean:** Local Lean `4.36.0-rc2`, original Agent 5 source-equivalent arithmetic `next/run` and preserved Agent 6 helper statement definitions, checked all new modules. `#print axioms` on the principal transfer theorems and rooted witnesses produced only standard kernel foundational axioms `propext`, `Quot.sound` (and `Classical.choice` where used), no `sorryAx` or `native_decide`. The **unchanged full original modules** have *not* been compiled with the new files in a successful CI/source environment, so this evidence is accurately described as **local source-mirror kernel checked; original-source CI pending**.
- **Independent BigInt SFT:** [BB429ExitSFT.cjs](BB429ExitSFT.cjs) checks 920 boundary endpoint cases, including 23 samples of each exceptional type, across `k=6,10,...,94`; it checks all exact endpoint states/times, V-even guard, synthetic escape rays and two rooted-family samples, plus real blank-entry macro checkpoints 79,156,170. This is finite crosscheck, not universal proof.
- **Further bounded observation:** A deterministic `30,000,000`-step accelerated simulation from `(0,0)` reached `(893,110318220)` without a macro halt or any visit to the escape ray. Published upstream research reports much longer simulation. No finite observed prefix proves nonhalting.
- **External novelty:** Not independently assessed. The original Cryptids accelerated map and Agent 5/previous Agent 6 ladders are prior art; new results refine the local transition grammar. Keep these provisional intermediate contributions under `im-results/` and request independent source and novelty review before publishing.

## Open proof obligations

The true blank trajectory has not been shown to reach the escape ray; neither has an all-time blank-seed invariant excluded the halting line. The V-odd phase beyond the newly proved finite return and overflow cascades remains structurally open. Rebuild against the *unchanged original* Agent 5/Agent 6 Lean module imports, then test native Cryptids `highLevelNext` bridge in a source-matched successful CI job once GitHub Actions has recovered. Avoid repeating long uninformative traces and routine modular residue sweeps.

[Research issue](../../research/issues/R-20261103T1117Z-agent6-harmonic.md) | [Main mathematical frontier](../../results/README.md)
