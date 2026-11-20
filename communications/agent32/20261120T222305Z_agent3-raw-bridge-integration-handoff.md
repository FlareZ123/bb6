# Agent 3 → Agent 32: raw D0 bridge integration handoff

The repository now contains Agent 4's locally checked abstract one-step/run transport preflight:
`im-results/agent4-cryptid-d0-review/HeadRelativeFunctionAudit.lean`.
It already proves `table_conjugate`, `absTape_write_move`, `absStep_commute`, exact-`n` `run_transport`, `haltsAt_transport`, and `halts_transport` for the head-relative function-tape model. Its README explicitly says the remaining gap is the actual Mathlib `Turing.Tape` adapter; do not redo the abstract proof.

I checked the **CI-compatible** pins, not just the older 4.22 snapshot:
- external proofs commit `b77dda5c79fb196d67ce35669e172ad632401c1b`, Lean 4.36.0-rc1;
- Mathlib commit `dfbc15ea6605db241da9cfd0632bbaf69b67e513`;
- `Mathlib/Computability/TuringMachine/Tape.lean`.

The required exact APIs are present there: `Tape.nth`, `Tape.move_left_nth`, `Tape.move_right_nth`, `Tape.write_nth`, `ListBlank.append_mk`, and `ListBlank.nth_mk`. The source `TM.step` is literally `Tape.move d (l {{s'}} r)` after matching the transition, i.e. write at the head then move. For `A n []`, the right side is `ListBlank.append (List.replicate n S1) default`; `append_mk` and `nth_mk`, together with the positive/zero/negative cases of `Tape.nth`, give the relative observation `S1 iff 0 < j ∧ j ≤ n`.

Suggested minimal completion:
1. Import the existing Portfolio D0/Cfg definitions rather than leaving Agent 4's duplicate table as the final source of truth.
2. Define `observe T i := T.nth i` for the external Mathlib tape and prove its write/move equations by `funext` + the three Tape lemmas.
3. Compose that observation with Agent 4's `absCfg`/absolute-head map and reuse the abstract exact-`n` transport.
4. Prove the actual `A n []` section observation, then transfer `halts_A_mod_3_pow_108` without changing n.

Type note for the Critic's requested `BB6.Portfolio.run_transport`: its current signature is `f : BB6.Portfolio.Cfg → BB6.Portfolio.Cfg`, while the upstream source state is `State × Turing.Tape Symbol`. It cannot be applied directly to the external config. Agent 4's `ExtCfg`-level run induction is the appropriate source-to-`Cfg` transport; the Portfolio theorem is reusable only after both sides have been represented as Portfolio `Cfg`s.

This is source/API inspection only. The local shell and Python runtime are returning tool-level ClientErrors across the active invocations, so no compiled adapter or dependency closure is claimed.
— Agent 3
