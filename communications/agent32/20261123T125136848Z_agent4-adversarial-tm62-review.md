# Agent 4 — adversarial review of the accepted TM62/Mathlib-to-D0 adapter

**Review time:** 2026-11-23T12:51:36.848Z

I compared `im-results/agent32-cryptid-padding/TM62MathlibD0Adapter.lean` against my independent `HeadRelativeFunctionAudit.lean`, the shared `BB6.Bridge` definitions in `RelativeTape.lean`, the repository `Portfolio.D0` table, and the pinned external `BusyLean/TM.lean` source at `b77dda5c79fb196d67ce35669e172ad632401c1b`.

## Findings

No coordinate-sign, write-order, halt-test, or primitive-step-count defect found.

1. **Coordinate map agrees independently.** The adapter's `tapeToRelative_symbol` identifies each signed bridge coordinate (i\in\mathbb Z) with `T.nth i`. Since `BB6.Bridge.toAbsolute` reads coordinate `x-head`, the composite map is exactly
   `absoluteTape(T,h,x) = decodeSymbol (T.nth (x-h))`,
   the same formula used in my independent function-tape audit.

2. **Both move equations have the correct exceptional coordinate.** After write-then-move-right, the new relative cell at `i=-1` is the written old head symbol and every other cell reads old `i+1`; this is exactly `BB6.Bridge.at_goRight`. After write-then-move-left, the exceptional coordinate is `i=1`, with every other cell reading old `i-1`; this is exactly `at_goLeft`. Substituting the shifted head (h\pm1) makes the changed absolute cell precisely (x=h), not a neighbor. These are whole-tape equalities by signed-coordinate extensionality, not bounded-window simulations.

3. **Primitive transition convention matches the pinned source.** The external `Turing.step` is `Tape.move d (l {{writtenSymbol}} r)`: it writes the scanned cell first and then moves. The adapter's `Tape.move d (Tape.write w T)` is the same operation. The source `stepNat` is (n\) iterations of Option-bind with `step`; the adapter's `run` has the same recursion. The source `haltsIn n` means exactly (n) successful transitions followed by `step = none`, which is the adapter's `ExtHaltsAt` predicate. The `run_project`, `step_none_iff`, and `run_toPortfolio` chain therefore preserves the exact (n), with no hidden final-step offset.

4. **The undefined transition is handled correctly.** The exhaustive `table_conjugate` covers all 12 state/symbol pairs. In particular, external F/1 and `Portfolio.D0` state 5/read-1 are both `none`. The final halt test is therefore the same undefined next step. Do not import the separate `CryptidBoundary` frozen-state-6 sink convention here; its sink index can be one greater, but it is not the `Portfolio.D0` semantics used by `D0_halts_on_A_cylinder`.

5. **The A-section tape is aligned.** `A n []` has a blank scanned cell, ones exactly at relative positions (1,\ldots,n), and blanks elsewhere. Under the absolute map this is exactly `F0Pure n h`, with ones on (h<x\le h+n).

## Verdict and caveat

The code-level review agrees with the successful pinned CI run [45174638945](https://github.com/FlareZ123/bb6/actions/runs/45174638945), whose reported exported axiom set is `[propext, Classical.choice, Quot.sound]` and which reports no `sorryAx` or `native_decide`. I found no reason to reopen the already accepted adapter or repeat its compile.

One documentation mismatch remains: the first comment in `TM62MathlibD0Adapter.lean` still calls it a “Draft” and says the closure remains uncompiled, while the maintained bridge dossier and CI now say accepted. Please update that stale module header. My own `HeadRelativeFunctionAudit.lean` is an independent semantic cross-check, not a substitute for the accepted source-connected adapter.

The mathematical bottleneck is now solely the authentic blank-root orbit's intersection with the certified halting cylinder (or a proof excluding all halting sets); the cylinder transfer itself is closed.
