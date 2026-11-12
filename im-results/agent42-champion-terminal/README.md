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

Use Python's standard `base64` and `lzma` libraries (and `tarfile` for the first archive) to decode. The manually triggered [workflow](../../.github/workflows/agent42-champion-terminal-source.yml) compiles `TerminalFinish.lean`, the authoritative `TerminalLeft.lean`, `TerminalBridge.lean`, and `TerminalChampion.lean` against the unmodified original `Frontier`, `Symmetry`, `RootShift`, and `ChampionRootBridge` imports using Lean **4.36.0-rc2**. [CI 42739779283](https://github.com/FlareZ123/bb6/actions/runs/42739779283) completed successfully, with no errors or `sorry`. `#print axioms literalS1_section` is `[propext, Quot.sound]`; `#print axioms literalS1_terminalExact` is `[propext, Classical.choice, Quot.sound]`. Other individual arithmetic and run lemmas have similarly standard-only audits. A Lean linter warning for an unused simp argument is harmless.

## Critical remaining mathematical work

This verifies **one** important source-table terminal macro formula. For the published champion's exact global step score, the all-parameter counted `Inc0`, `Rst0/Rst1/Rst2`, reset-core and drain transitions remain unproved (see [Agent24](../agent24-champion-time/README.md)). The source-machine transport and undefined final halt-query convention are now proved. The next productive step is counted composition of the champion's long itinerary using [Agent24's](../agent24-champion-time/README.md) still-conjectural increment and reset costs and [Agent48's rooted six-step transport](../agent48-champion-root/README.md). This work supplies no universal upper bound for BB(6), no independent scored full champion halt, and no open holdout decision. Accordingly it belongs in `im-results/`.


## Blank-prefix to champion-score interface

[TerminalAfterPrefix.lean](TerminalAfterPrefix.lean) closes the final composition edge. Given any original-source TM63 blank run of `n` successful moves that reaches state D on a tape satisfying `TerminalFinish.SectionBits L a`, `tm2_halts_after_terminal_prefix` proves the source machine halts after `n + 59 + 12*(L+a)` successful moves. The root-corrected `champion_halts_after_terminal_prefix` and `champion_attainable_after_terminal_prefix` then give the six-state champion score `n + 59 + 12*(L+a) + 7`, with the six-step root offset and final undefined transition query both accounted for. The only remaining premise is the genuine counted blank-prefix run to that terminal section; no assumption is made about the tape exterior. This is a reusable conditional join, not yet a champion witness because the full counted prefix is not proved.
\nThe new prefix-join leaf is included in the existing manual-only source workflow, but it has not yet been run through that workflow in this invocation. Treat its statements as a pending Lean proof candidate until the pinned compile succeeds. Local shell/Python execution was unavailable here, so I have not claimed a kernel-checked result.\n