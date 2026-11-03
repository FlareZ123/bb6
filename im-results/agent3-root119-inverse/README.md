# Root119 / auxiliary TM2153: exact physical halting-gate reduction

**Status (2026-11-03, Agent 3): intermediate, fully standalone Lean-kernel checked against the literal auxiliary table.** No new nonhalting or halting decision for the genuine blank root. No claim of academic novelty or of an improved BB(6) bound.

## Exact machine and proof

The six-state two-symbol auxiliary has literal RLE `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`; state A reading 1 is the unique undefined instruction. It is the published BusyCoq `Eqv_v2.TM2153` counterpart of historical deleted #119 `1RB1LB_1RC---_1LD1LF_1LE0LD_0LA1RF_1LC0RE`. The earlier agent12 regression [test-root119-eqv.cjs](../agent12-r001-source/test-root119-eqv.cjs) validates their state relabeling and exact finite merging at 315075/337226 primitive steps, **not** their unknown global disposition.

Lean source: [Root119Gate.lean.xz.b64](Root119Gate.lean.xz.b64), SHA-256 of **decoded UTF-8 Lean source** `f0b6d42d009e195a6fad6594aa282b8e3de0751141755ec98ee2dcb929b991bd`. Decode using Python standard libraries `base64.b64decode` followed by `lzma.decompress`; run with Lean **4.36.0-rc2**, `import Std`. The compressed text is deliberately retained as a reproducible exact byte artifact, without any source substitution.

The module declares an exact `State`, `Cfg` containing full arbitrary `Int → Bool` tape, raw `step : Cfg → Option Cfg` with the **twelve** literal source cells (including unique halt), `blank` and `run`. Its final theorem is

```lean
Root119.blank_halts_iff_Cgate :
  (∃ n : Nat, Root119.run n = none) ↔
  (∃ k : Nat, ∃ x : Root119.Cfg,
     Root119.run k = some x ∧ Root119.Cgate x)
```

where `Cgate x` means state C, scanned bit 0, three leftward bits `0,1,1` at head offsets -1,-2,-3. Other certified lemmas:
- `d0_gate`: entering D/0 reads the two left bits; if both are 1, the next two physical steps arrive at A/1, hence undefined.
- `danger_from_C` and `three_predecessor`: every A/1 stopping configuration actually encountered after a normal three-step predecessor chain originates from that C/0 011 gate; the alternative F/1 predecessor of D/0 has just cleared its own cell, ruling out danger.
- `Cgate_four_step`: from any full infinite tape satisfying the gate, the fourth raw transition is undefined.
- `halting_run_has_Cgate`: three-predecessor extraction for arbitrary genuine blank time with the initial three positions checked separately.

**Local verification:** Lean 4.36.0-rc2 compiled all declarations on 2026-11-03, and `#print axioms Root119.blank_halts_iff_Cgate` reported exactly `[propext, Quot.sound]`, likewise the local gate and predecessor theorems, without `sorry` or arbitrary axioms. This is a *standalone verbatim-table semantics* check, not a direct source-import compilation of the original BusyCoq Coq/Rocq proof or its equivalence theorem. State renaming and blank coalescence rely on preexisting Agent12 work.

**Finite observation:** independent Python sparse-tape literal interpreter checked 2,000,000 raw steps from the auxiliary blank configuration (no A/1, no D/0 with both left cells 1); 8344 A entries all saw 0. This finite prefix is neither a nonhalting proof nor a certified primitive runtime. A radius-16 nondeterministic boundary-window overapproximation admits a spurious 93-transition A/1 path, so such naive finite-window closure does not prove avoidance.

## Exact unbounded C-sweep and synthetic fatal-word family (additional local Lean proof)

[Root119Sweeps.lean.xz.b64](Root119Sweeps.lean.xz.b64) has decoded Lean-source SHA-256 `1d7480f36df69f95fc621622e81ebd5548209a1ebe5f4678cd90f85b41c2b8cc`. Decode using the same Python `base64` + `lzma` procedure and compile `Root119Gate.lean` to a `Root119Gate.olean` prerequisite before compiling `Root119Sweeps.lean` with that module on the Lean search path. Both compiled locally under Lean 4.36.0-rc2.

- `C_one_sweep` proves for **every n** that a C-state scanning n consecutive 1-cells to its left exactly erases them, moves n cells left, and preserves every other physical tape cell. Full exact `eraseLeft` tape function, no execution cutoff.
- `C_sweep_halts`: if the first n scanned C-cells are 1 and the next four symbols in the leftward direction are **0,0,1,1**, then the literal auxiliary machine halts after the next four actions. Valid for arbitrary n and other tape cells.
- `A_zero_one_run_halts`: for every n>=1, an **arbitrary synthetic** A/0 entry with a zero right neighbor, n−1 consecutive 1s to the left, followed by **0,0,1,1**, runs directly to the undefined instruction and is halted by raw time **n+6**. Thus one cannot prove safety merely by asserting an A entry scans zero. The special synthetic case n=1 is fatal after seven attempted `run` transitions; its first undefined instruction is encountered at primitive index six.
- All three final `#print axioms` outputs are exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. This source is locally source-table faithful, but has **not** been imported into original upstream Coq/Rocq; do not imply upstream theorem certification or a root decision.

The sweeping family provides a quantified stress test for candidate true-blank A-entry language invariants. A real proof must exclude these **synthetic** fatal words from the actual fixed blank history, while also controlling the F-branch sources of C sections. Only the earlier `blank_halts_iff_Cgate` currently states a full necessary/sufficient genuine blank-halt criterion.

## Remaining obligations

Prove genuine blank-run nonreachability of `Cgate`, or exhibit a true run reaching it. Ideally derive a closed source-connected return-language/inductive invariant, rather than extending finite traces or proving more synthetic local facts. If either rooted outcome is decided, transfer the result through the published `Eqv_v2.TM2153` equivalence after independently checking its actual blank-root semantics and assumptions. Original BusyCoq source pin: `ccz181078/busycoq@33209bc7dc282b38c8cd6be507bfc551fea56108`, `verify/Eqv_v2.v`.

Programme: [R-20261103T1154Z-agent42-root119-trap](../../research/issues/R-20261103T1154Z-agent42-root119-trap.md). Agent42 investigates the **forward** A-entry guard; Agent3's independent task here supplied the **inverse** all-time gate theorem. Keep in `im-results/` until a root classification or independently reviewed substantive mathematical breakthrough.
