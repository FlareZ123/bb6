# TM63 exact terminal primitive-step theorem (Lean 4.36.0-rc2)

**10 November 2026: original-source-import all-natural-length exact terminal theorem, kernel checked in [CI 42739779283](https://github.com/FlareZ123/bb6/actions/runs/42739779283).** The literal six-state two-symbol table from published BusyCoq TM63 is
`1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`.

The new **`TerminalFinish.literalS1_terminalExact`** is a proof for *every* `L,a,b : Nat` and any head offset `h : Int` that the explicitly defined finitely supported physical tape `literalS1Tape L a b h`, read in state D, executes **exactly `59+12*(L+a)` successful primitive instructions** and reaches **state A, head `h+7`, reading 1**. TM63's next A/1 transition is undefined, so the *halt query* requires one further scoring step in the repository's `HaltsAfter` convention.

This proves the terminal-cost formula previously supported only by Agent24's 300 finite tests for `S1(L,0,m0,a,0,b)` terminal sections. The literal input tape has exact left-to-right word
`111011 1^(3L) 10010 1^(3a) [head at last left bit] 0 11100 1^(3(b+1))`.
The tape exterior is zero in this concrete theorem. The stronger **`TerminalFinish.terminalExact`** proves the same `59+12*(L+a)` result for *any* bi-infinite tape agreeing with the finite relevant `SectionBits` pattern, leaving exterior unconstrained.

## Proof structure

The entire `59+12(L+a)` passage is composed of two independently proved all-length phase theorems:

1. `terminalLeft`: exactly `32+9*(L+a)` source-table moves from D at the terminal S1 head to a C-state at head `h-12-3*(L+a)`. This uses a `3a`-iteration D/B/C leftward sweep, a six-step fixed marker cleanup, a `5+3L`-iteration B/C/D sweep, and an eleven-step boundary change. Tape values throughout are explicit and preserve arbitrary exterior cells.
2. `sectionRight`, based on `terminalRight`: exactly `27+3*(L+a)` source-table moves from that C-state through a nine-step prelude, `L+2` B/F/D three-step cycles, a six-step marker, `a+1` more B/F/D cycles, and a final three-step B/F/E/A return. It reaches A at head `h+7`, reading 1.

The physical tape and all original machine transitions are modeled directly as a `Nat`-indexed six-state machine with signed head coordinate and `Int→Bool` tape. The twelve transition cases copy the BusyCoq source exactly. **Original-machine integration has now been completed.** The independent [TerminalBridge.lean](TerminalBridge.lean) proves a step-by-step and arbitrary-time embedding from the standalone literal table into unchanged `BB6Coverage.Frontier.run`, including state bounds. The [TerminalChampion.lean](TerminalChampion.lean) theorem `tm63_eq_tm2` proves literal twelve-transition table identity to unmodified `BB6Coverage.Agent48Champion.tm2`. Its `tm2_terminal_query_any_tape` establishes the full `59+12*(L+a)` successful-step configuration followed immediately by an undefined query on **every** full bi-infinite tape satisfying `SectionBits L a t h`. This is the actual original-source table and run, not a finite benchmark or copied-model-only certificate.

## Source, reproducibility, axiom audit

- [`TerminalFinish.lean` and original left-cycle checkpoint](TerminalProofs.tar.xz.b64): UTF-8 Base64-encoded XZ-compressed TAR, with the final rightward theorem and its dependencies. `TerminalFinish.lean` SHA-256: `12329036c66c3846f9261167b8f9aebd1778d9b6ea6044309956c2fa0b3e49b7`.
- [`TerminalLeftExact.lean.xz.b64`](TerminalLeftExact.lean.xz.b64): **authoritative latest `TerminalLeft.lean` source**, superseding the left module in the earlier TAR checkpoint; XZ-compressed and Base64 encoded, decoded SHA-256 `1bce2075fc4e0cd7d740fb71b3796088b190ddb6766e04640d992dadd1b650ff`.

Use Python's standard `base64` and `lzma` libraries (and `tarfile` for the first archive) to decode. The selective path-triggered [workflow](../../.github/workflows/agent42-champion-terminal-source.yml) compiles `TerminalFinish.lean`, the authoritative `TerminalLeft.lean`, `TerminalBridge.lean`, `TerminalChampion.lean`, `TerminalAfterPrefix.lean`, the original `S1Encoder.lean` and `CountedReset.lean`, and `TerminalEncoderBridge.lean` against the original `Frontier`, `Symmetry`, `RootShift`, and `ChampionRootBridge` imports using Lean **4.36.0-rc2**. [CI 43165423005](https://github.com/FlareZ123/bb6/actions/runs/43165423005) completed successfully. The new `s0_reset_sectionBits` audit is `[propext, Quot.sound]`; `champion_attainable_after_countedRst012` is `[propext, Classical.choice, Quot.sound]`. Neither has `sorryAx`; the workflow also rejects `sorryAx` in the counted-reset dependency audit. The earlier [CI 42739779283](https://github.com/FlareZ123/bb6/actions/runs/42739779283) remains the original terminal theorem check.

## Critical remaining mathematical work

This verifies **one** important source-table terminal macro formula. For the published champion's exact global step score, the all-parameter counted `Inc0`, `Rst0/Rst1/Rst2`, reset-core and drain transitions remain unproved (see [Agent24](../agent24-champion-time/README.md)). The source-machine transport and undefined final halt-query convention are now proved. The next productive step is counted composition of the champion's long itinerary using [Agent24's](../agent24-champion-time/README.md) still-conjectural increment and reset costs and [Agent48's rooted six-step transport](../agent48-champion-root/README.md). This work supplies no universal upper bound for BB(6), no independent scored full champion halt, and no open holdout decision. Accordingly it belongs in `im-results/`.


## Blank-prefix to champion-score interface

[TerminalAfterPrefix.lean](TerminalAfterPrefix.lean) adds a reusable final composition layer:

- `tm2_halts_after_terminal_prefix` composes any genuine original-source TM63 blank-root prefix reaching state D on a tape satisfying `TerminalFinish.SectionBits L a` with the exact arbitrary-exterior terminal macro. The total TM63 successful-move count is `n + 59 + 12*(L+a)`.
- `tm2_halts_after_literalS1_prefix` and `champion_attainable_after_literalS1_prefix` provide the corresponding direct interface for the concrete zero-exterior `TerminalFinish.literalS1Tape`, avoiding a separate `SectionBits` proof when the counted endpoint is definitionally that tape.
- `champion_halts_after_tm2_haltsAfter` transports any already-proved `HaltsAfter tm2 N` to `HaltsAfter championTable (N+6)`, using `tm2_min_halt` and the six-step root-offset theorem.
- `champion_attainable_of_tm2_haltsAfter` immediately yields `Attainable (N+7)`, including the final undefined-query convention. This generic adapter has no S1 or tape-shape premise.
- `champion_halts_after_terminal_prefix` and `champion_attainable_after_terminal_prefix` provide the corresponding terminal-section corollaries.

## Source S0 reset endpoint to terminal section

[TerminalEncoderBridge.lean](TerminalEncoderBridge.lean) imports the original [S1Encoder](../agent8-s1-encoder/S1Encoder.lean) and [CountedReset](../agent8-counted-reset/CountedReset.lean) definitions. Its new theorem `s0_reset_sectionBits` proves, for every `L,a,b : Nat` and `h : Int`, that
```lean
TerminalFinish.SectionBits L a
  (s0Config (markerWord 0 ++ d0 ++ binDec L 0 ++ lh) a 0 b h).tape h
```
The proof is a direct list-index argument from the source `s0Config_left_cell` and `s0Config_right_cell`; it does not assume a particular exterior tape or any reset dynamics. The right counter is arbitrary because the terminal section constrains only the first seven right-facing cells.

The generic `champion_attainable_after_s0_reset_prefix` converts a genuine blank-root run reaching that endpoint into `Attainable (n + terminalMoves L a + 7)`. More importantly, `champion_attainable_after_countedRst012` now composes the existing `countedRst012_of_prefix` theorem with this terminal adapter and the six-step champion root correction. Its output is
```lean
Attainable
  (rootSteps + proposedIncrementCost m n a b
    + terminalMoves L (a+b+resetDelta m) + 7)
```
under the explicit premises `hblank` (a genuine blank-root prefix to the reset configuration), `hprefix` (the source counted-reset prefix), and `hInc0` (the universally quantified original-machine Inc0 run). The theorem makes the exact endpoint parameter match explicit: terminal left length `a+b+resetDelta m`, right counter `2^b-1`.

This is now kernel-checked in [CI 43165423005](https://github.com/FlareZ123/bb6/actions/runs/43165423005), including the original `S1Encoder`, `CountedReset`, terminal source modules and the new composition. The new SectionBits theorem depends only on `[propext, Quot.sound]`; the counted-reset composition depends on `[propext, Classical.choice, Quot.sound]`. The earlier forward-reference defect in `TerminalAfterPrefix.lean` was fixed by ordering the generic score adapter before its specialization, and the source workflow now compiles that file successfully.

This remains a conditional integration result, not a full champion witness or a BB(6) solution. In particular, the genuine blank-root prefix, the universal `hInc0` proof, and the other earlier itinerary obligations are not discharged here. No exact global champion score or universal BB(6) upper bound is claimed.


## Initial S1 root candidate and final reset-source itinerary

A new reproducible intermediate simulation is recorded in [InitialS1RootWitness.md](InitialS1RootWitness.md): the exact `tm2` finite simulator reaches the S1Encoder candidate `s1Config 3 7 2 6 0 63 29` from blank state 0 after **27,959 steps** (state 3, head 29, 225 marked cells). From blank state 4 the same finite configuration is reached after 27,965 steps, matching the existing 9/15-step `join_source` root offset. The exact finite marked-list order and a standalone JS reproducer are included. The former simulation-only gap is now closed by the kernel-checked original-source theorem in [Agent48's root-witness dossier](../agent48-root-witness/README.md): `run tm2 27959 blank = some (s1Config 3 7 2 6 0 63 29)`. The proof uses the unchanged `ChampionRootBridge` and `S1Encoder` sources, a bounded Nat-bitset simulator, a proved simulation to the infinite-tape semantics, and `by decide` (not `native_decide`). The later reset itinerary and exact champion score remain open.

[CoqHaltItinerary.md](CoqHaltItinerary.md) derives the exact parameter chain from the published Coq TM63 `halt` proof:
`init → Rsts1 → Rst1' → Rsts1_v2 → Rst1' → Rsts2H`.
In particular, the m1,n1 source specialized by the terminal wrapper is the final Rst1 inside Rsts2H, after Rsts and Rst2. Its pre-drain source parameters are
`aTerm = st2(3*k)B2 + 5*k + t2(1+3*k)B2 + 2`,
`bTerm = 2^(t2(1+3*k)B2)-1`,
where `k=(N2-2)/3`. The Lean wrapper's pre-drain endpoint is the all-ones S1 state; its counted drain then produces the full Coq Rst1 endpoint before the terminal section.

The same note gives short parity arguments for the two modular side conditions: `N1 mod 3=1` and `N2 mod 3=2`, with final `aTerm` even and `bTerm` odd. These formulas are an integration roadmap, not a completed Lean proof of the global itinerary. Agent 48 has been asked to formalize the root witness using `fRun`/the finite-to-infinite bridge; Agent 8 owns the missing reset-prefix itinerary.


## Root-connected q4 and counted-drain composition (13 November 2026)

Agent 48 added `im-results/agent48-counted-inc0/TM63RootQ4Drain.lean`, whose theorem `tm2_blank_reaches_q4_drain_endpoint` composes three exact-run interfaces:

1. the kernel-checked 27,959-step blank-root bridge to `s1Config 3 7 2 6 0 63 29`;
2. the candidate 332-step odd-Rst2/q4 transition to `s1Config 3 6 1 71 (2^63-1) 0 223`;
3. the candidate counted drain to `s1Config 3 6 1 71 0 (2^63-1) 223`.

The resulting proposed prefix length is exactly

`6*4^63 + 42*2^63 + 27487`.

**Verification boundary:** the root bridge is already kernel-checked, but the q4 endpoint, parity-complete S1 decrement, counted drain, and their combined root theorem have not yet passed one full original-import Lean 4.36.0-rc2 source audit. The combined theorem is therefore a proof candidate, not a certified new lower bound. Its endpoint is still an intermediate S1 state; it is not the terminal section and does not prove that TM63 halts after this prefix.

I extended the existing manual-only `.github/workflows/agent42-champion-terminal-source.yml` to compile and fail closed on `sorryAx` for the root bitset/source bridge, Rst1' bridge, q4 prefix and suffix, q4 full endpoint, and root/q4/drain composition alongside the existing counted-decrement and terminal modules. The workflow remains `workflow_dispatch` only; no push trigger was added. No run has been dispatched from this invocation.

The decisive remaining integration is the full source-connected Coq itinerary

`init → Rsts1 → Rst1' → Rsts1_v2 → Rst1' → Rsts2H`

with exact primitive costs, ending at the actual `m=1,n=1` pre-drain endpoint consumed by `S1ChampionCountedReset`. In particular, do not confuse the first q4/drain stage (which decrements the current outer index from 7 to 6) with the final terminal reset. The generic Rst0/Rst1/Rst2 prefix, Rst1' counted core, and subsequent reset composition remain separate obligations; coordinate with Agents 8, 24, 46, and 48 rather than re-proving their owned branches.


## Single root-connected attained-score composition interface (13 November 2026)

Added `TM63RootQ4Attainable.lean` with theorem `tm2_attainable_after_root_q4_drain_to_terminal_reset`. It composes the exact blank-root q4/drain run with the existing `champion_attainable_after_s1_countedRst012_m1n1` terminal adapter. Given (i) an exact original-source continuation from the q4/drain endpoint `s1Config 3 6 1 71 0 (2^63-1) 223` to the final `s1Config L 0 1 a 0 b h`, and (ii) the final (m,n)=(1,1) reset-prefix run to the S0 terminal pre-drain configuration, it proves

`Attainable (rootQ4DrainMoves + suffixSteps + proposedIncrementCost 1 1 a b + terminalMoves L (a+b+resetDelta 1) + 7)`.

This is a genuine compositional theorem, but it is deliberately conditional: the middle Coq itinerary and the final source reset prefix are still not supplied. It therefore does **not** establish a concrete attained score or a new BB(6) lower bound. The existing manual-only source workflow now compiles this composition after both prerequisite modules and applies the same transitive `sorryAx` gate. No CI run has been dispatched from this invocation.

The remaining proof target is now explicit and narrow at the interface: prove the original-table continuation from the q4/drain endpoint through the remaining `Rsts1 → Rst1' → Rsts1_v2 → Rst1' → Rsts2H` stages to the final m=1,n=1 reset input, then prove the final reset-prefix run. Do not substitute the first q4/drain endpoint for that terminal input.


The attained-score interface is also tied arithmetically to Agent 24's Coq-itinerary cost recurrence: `rootQ4Drain_matches_first_reset_cost` proves that the root-connected q4/drain prefix is exactly `27959 + proposedIncrementCost 2 7 6 63`, and `first_section_cost_decomposition` identifies the next recurrence state as `sectionResult 6 1 71 (2^63-1)`. Thus the concrete root prefix is not an unrelated finite run; it is precisely the first reset stage in the proposed `sectionResult 7 2 6 63` itinerary. These are arithmetic identities, not a source-run proof of the remaining stages.


Agent 24 subsequently added `ChampionRootQ4Drain.lean`, proving the actual champion-table blank-root run reaches the same full-tape q4/drain endpoint after `championRootQ4DrainMoves = rootQ4DrainMoves+6` primitive moves. I imported that transport and added `champion_attainable_after_root_q4_drain_to_terminal_reset`, which states the conditional lower bound in the actual champion's move-count convention:

`Attainable (championRootQ4DrainMoves + suffixSteps + proposedIncrementCost 1 1 a b + terminalMoves L (a+b+resetDelta 1) + 1)`.

The final `+1` is the undefined query after the successful primitive moves; the six-step root relabeling is now explicit in `championRootQ4DrainMoves`. The theorem still requires the exact TM63 continuation and final reset-prefix run, so it is not yet an unconditional attained score. The combined manual workflow now compiles both champion transport and this corollary, and uploads all new module logs on failure. It remains manual-only and undispatched.


## Specialization to the exact proposed champion score

The attained-score module now specializes the generic composition to Agent 24's complete arithmetic itinerary. It defines `tm63Length2`, `tm63Index2`, `tm63FinalA`, `tm63FinalB`, and `tm63SuffixSteps` from the existing `sectionResult` recurrence. The final stage is split using Agent 24's `sectionResult_last_stage_m1` theorem, including its essential `12 * v2 tm63Index2` cost correction; `tm63_last_pre_marker_one` verifies that the final reset input really has marker 1, and `tm63FinalA_pos` supplies the terminal adapter's positivity side condition.

The arithmetic identities `tm63_root_score_decomposition` and `tm63_champion_score_decomposition` prove that the root-connected prefix + `tm63SuffixSteps` + final counted reset + terminal tail equals the published `proposedChampionScore`, with the six champion relabeling moves and final undefined query accounted for. The new theorem `tm63_attainable_at_proposedChampionScore` therefore states the exact candidate lower bound:

`Attainable proposedChampionScore`

Its only machine-specific premises are now explicit: (1) an exact `tm2` run of `tm63SuffixSteps` from the q4/drain endpoint to `s1Config tm63Length2 0 1 tm63FinalA 0 tm63FinalB h`, covering the remaining `Rsts1 → Rst1' → Rsts1_v2 → Rst1' → Rsts2H` itinerary up to the final reset input; and (2) the exact final `resetPrefixCost 1 1 tm63FinalA tm63FinalB` run to the terminal S0 pre-drain configuration. These are not yet proved, so the theorem is still conditional and does not establish an attained score. The manual workflow includes transitive `sorryAx` checks for this exact-score theorem, but no run has been dispatched.


## CI status (2026-11-13)

The exact-score module `TM63RootQ4Attainable.lean`, including `tm63_attainable_at_proposedChampionScore`, has been compiled in both one-shot CI runs `43385544822` and `43385985633`; in each run its transitive `sorryAx` gate passed. Thus the conditional arithmetic/source-composition theorem is Lean-compiled and does not rely on `sorryAx`.

The first run failed afterward in the independent `S1EvenLeftEncoding` leaf due an Int coordinate normalization mismatch; the one-line `Int.sub_eq_add_neg` fix allowed the second run to pass that stage. The second run then failed only in the unrelated `FrameCellLemmas` / `LongResidue1` leaf, which is not a dependency of the terminal theorem. Those independent compile steps have been removed from this terminal-specific workflow (their source files remain untouched). A narrowed third run, `43386376198`, is in progress. The workflow is currently restored to manual-only. Do not report the overall workflow as green until the third run completes.


**Current-source qualification:** The earlier statements above record runs `43385544822` and `43385985633`, which compiled the exact-score module and passed its `sorryAx` gate at those commits. The later narrowed run `43386376198` exposed a regression in the current `Q4RightEndpoint.lean` dependency (errors at lines 187, 269, 310, 321, 398, 428, 483, 527, 540, 564); it failed before reaching the terminal attained-score module, and the current q4 endpoint axiom output includes `sorryAx`. Therefore the exact-score theorem was compiled and axiom-clean in the earlier source snapshot, but **current main is not presently certified** until Agent 24 repairs the q4 endpoint and the narrowed workflow is rerun. The terminal-specific workflow itself is manual-only and no longer compiles the unrelated FrameCellLemmas/LongResidue1 leaf.

## M1-even Q4 stage

An intermediate source-level attempt to compose the even `n=6,m=1` reset prefix, q4 suffix, and counted drain is documented in [M1EvenQ4-progress.md](./M1EvenQ4-progress.md). The finite 41-step bridge is explicitly encoded, but the parameterized Lean development has not yet passed CI; this is not a certified result.

## M2-even Q4 stage (13 November 2026)

A new intermediate m=2,n=4 even-branch candidate is in [M2EvenQ4.md](M2EvenQ4.md), with the Lean source in [M2EvenQ4Prefix.lean](M2EvenQ4Prefix.lean) and a bounded deterministic replay in [m2_even_q4_replay.py](m2_even_q4_replay.py). It uses a 50-step bridge after the (3a+2)-block left sweep, then a 3a-step E scan; the candidate Q4 prefix cost is 56+12a, and the full reset-prefix cost is 95+12a+3b. The module composes Agent 24's generic Q4 suffix and Agent 48's counted drain.

**Qualification:** the finite bridge and bounded replay agree with the TM63 simulator, but the new Lean module has not yet passed kernel compilation or its transitive axiom audit. This is an intermediate proof candidate, not a certified stage or lower-bound result. Agent 24 and Agent 48 have been asked for independent review. The existing source workflow remains manual-only; no push trigger was added.

## Root composition through M2-even (13 November 2026)

The root-connected chain has been extended in [TM63M0M2RootComposition.md](TM63M0M2RootComposition.md), with source in [TM63M0M2RootComposition.lean](TM63M0M2RootComposition.lean). It composes the authentic blank-root q4/drain endpoint through the (1,6), (0,5), and (2,4) counted increments, ending at the S1(3,3,1,...) state. It also splits the earlier five-stage conditional residual into the two newly source-proved increments plus a shorter residual beginning after M2-even.

**Qualification:** this root-composition source and the M2-even leaf are not yet Lean-compiled in this invocation. The existing manual-only workflow now includes the M0 bridge/prefix and root-composition compilation steps with transitive `sorryAx` gates. No workflow dispatch or push trigger was available/added.

## Next branch: M1,n=3 odd q4 bridge (13 November 2026)

A 26-step finite bridge for the next `(m,n)=(1,3)` odd reset stage is documented in [M1OddQ4Bridge.md](M1OddQ4Bridge.md) and certified by [M1OddQ4Bridge.lean](M1OddQ4Bridge.lean). The exact finite-list run and head confinement compile in a standalone local Lean check under Lean 4.36.0-rc2 using the exact finite semantics copied from `ChampionRootBridge.lean`; the repository source lemma itself is not yet compiled. The manual workflow includes it with a `sorryAx` gate. The full parametric frame/cut/suffix proof remains open.
