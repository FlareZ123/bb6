# Lean-checked coarse bound for the uncompressed SymRun prefix

This is an intermediate proof-engineering artifact for the F424/F412 Cryptids halting certificates. It does **not** establish a BB(6) result or close the symbolic SymRun primitive-time proof.

## What is proved

The two Lean files provide a source-faithful transcription of the relevant uncompressed engine definitions from the pinned upstream Cryptids revision `3647718b5df22e1a61462dec0376bd204526285a`:

- `MItem`, `SymMode`, `strictNat`, `strictMList`, `bumpM`, `prependZeroM`, `stepElemM`, `iterStep`, `stepElem16/256/4096`, and `runElemFast` (upstream `BusyBeaver/Calculi/HaltShared.lean`, around lines 2400–2608).
- The source wrappers `strictNat` and `strictMList` are definitional identity wrappers; the transcription retains them.

`PrefixGrowth.lean` proves:

1. `maxRunState (stepElemM s) ≤ maxRunState s + 1` for every state.
2. The nested `runElemFast a b c d` is exactly `iterStep stepElemM (4096*d + 256*c + 16*b + a)`.
3. A trace-maximum fold covers every intermediate state, not only the final checkpoint.
4. The complete F424 prefix (19,217 iterations from `(.CB, [], [.run 1, .run 0])`) has every run field at most 19,218.
5. The complete F412 prefix (19,255 iterations from `(.BB, [.run 0], [])`) has every run field at most 19,255.

`PrefixCostTable.lean` encodes the machine-specific source cost table:

- F424: `step_BB_run0 = 8`, `exit_R_A = 13`.
- F412: `step_BB_run0 = 6`, `exit_R_A = 11`.
- The only variable-cost uncompressed branches are `step_DL_run2(d)=3d+9+exit_R_A` and `step_CB_run0_run_pos(d)=3d+8+exit_R_A`; all other branches cost at most 9.

It proves that every encoded branch cost is bounded by `3 * maxRunState(s) + 22`, and that the entire cost-table sum for each prefix, including the entry and separate terminal transitions, is below `2^31`.

## Verification and limitations

Both files typecheck locally with Lean 4.36.0-rc2:

```sh
lean -o PrefixGrowth.olean PrefixGrowth.lean
LEAN_PATH=. lean PrefixCostTable.lean
```

The definitions were transcribed and checked against the pinned upstream source, rather than imported from its full Mathlib-dependent project. Consequently, the proof currently establishes the field-growth and cost-table arithmetic for the transcription. It does **not** yet prove that each `stepElemM` transition is realized by the stated number of primitive Turing-machine steps. That source-level `ReachesIn` / `multiStep` connection must be added in the upstream project using its machine-specific `execute` lemmas.

This result also does not discharge the separate symbolic-trace token-count obligation (the ≤94 token maximum) needed by the later `stepSym` cost estimate. See the Agent 42 audit in `communications/agent38/`.
