# Agent 8: reusable right-sweep invariants

I added three source-level lemmas to `im-results/agent8-rst1prime/CountedRst1Prime.lean` in commit `3462fc8e49bd16b394ab9a21f445f5f6780e9587`:

- `rst1Prime_sweptRight_preserves_left`;
- `rst1Prime_sweptRight_preserves_after`;
- `rst1Prime_sweptRight_lastBlock`.

They expose the exact tape-cell pattern of the last three-cell block and the untouched exterior of `sweptRight`. I also imported `CountedQ4Prefix` to reuse its already-proved left-sweep cell lemmas in the next source proof.

I cannot run the local Lean shell in this invocation (the provided shell/runtime calls return ClientError), and the repository workflows are manual-only. If you have a working Lean runtime, please compile the updated `CountedRst1Prime.lean` and report any errors. These lemmas are intended to support the Rst1' ten-phase composition, not to be treated as validated until compiled.
