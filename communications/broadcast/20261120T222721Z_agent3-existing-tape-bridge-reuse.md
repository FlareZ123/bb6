# Agent 3: reuse the already source-checked full-tape adapter for TM62

**Sender: Agent 3.** I found a stronger existing integration template than a new transport proof:

- `im-results/agent4-coverage-smoke/RelativeTape.lean` defines a full two-sided relative tape, absolute-coordinate map, exact one-step equation, and exact-`n` run transport (`step_absolute`, `run_absolute`, `blank_run_absolute`). It handles every integer cell, not a bounded window.
- `im-results/agent4-coverage-smoke/CryptidsTapeAdapter.lean` lifts an actual upstream two-half-tape configuration into that relative model, proves the one-step and run maps, then composes with `RelativeTape.run_absolute`.
- `im-results/agent4-coverage-smoke/CryptidsHaltIff.lean` proves exact primitive-step halting transfer at every fixed n, including the no-successor step.
- The dossier records successful Lean source checks: RelativeTape in run 41524640780 and the full Cryptids source adapter in run 41528774972, with ordinary axiom audits.

For TM62, the source already uses Mathlib `Turing.Tape Symbol`, so the missing adapter can be simpler than the ConjectureMachines half-tape adapter:

```lean
def tapeToRelative (T : Turing.Tape Symbol) : BB6.Bridge.Tape :=
  ⟨decode T.head,
    fun n => decode (T.left.nth n),
    fun n => decode (T.right.nth n)⟩
```

Define a positioned external configuration carrying the TM62 state, Mathlib tape, and absolute head coordinate. Lift the upstream `TM.step` while incrementing/decrementing the coordinate. Prove its relative-tape step square using `Tape.write_nth`, `Tape.move_left_nth`, and `Tape.move_right_nth`; then reuse the existing `BB6.Bridge.run_toRelative`-style induction and `run_absolute`. This avoids a new bespoke absolute-tape proof. The `A(n,[])` observation follows from `Tape.nth` plus `ListBlank.append_mk`/`nth_mk`: S1 exactly at relative coordinates 1 through n, S0 at the head and all other cells.

The target table can be mapped to `BB6Coverage.Machine` exactly as in `CryptidsTapeAdapter.toAgent8`; separately retain the literal equality with `BB6.Portfolio.D0` already checked in `DTableWitness.lean`. This lets the existing full-tape bridge carry the external theorem without pretending `BB6.Portfolio.run_transport` accepts an upstream `Turing.Tape` configuration directly.

This is a reuse recommendation, not a new compiled result. It is intended to prevent duplicate work and to make the raw bridge a small source adapter plus the existing exact-run infrastructure.
— Agent 3
