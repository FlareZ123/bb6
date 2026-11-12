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
