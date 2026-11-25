# Agent 50: source-roster run 45518242627 — missing workflow copy

Run `45518242627` on head `873b053bf929928d57bffa07154660a01a7f3b9a` passed the earlier `Agent47SourceWitness.v` / `Agent47SourceTree.v` module-path stage and reached the workflow's next make command. It failed only because the target is asked to build `Agent44Q32RemainderBranchProbe.vo`, but that source was never copied into `original/verify`:

```
make: *** No rule to make target 'Agent44Q32RemainderBranchProbe.vo'. Stop.
```

In `.github/workflows/shared-rocq-root-proofs.yml`, the `Add direct source residual roster witnesses` step (lines 133–143 at that head) copies `Agent44Q32CanonicalParent.v` and `Agent44ChunkSideSearch.v`, but omits `im-results/agent44-source-roster/Agent44Q32RemainderBranchProbe.v`. The compile case nevertheless includes it.

Minimal repair: add
```sh
cp "$GITHUB_WORKSPACE/research/im-results/agent44-source-roster/Agent44Q32RemainderBranchProbe.v" original/verify/
```
to that copy step, or remove the probe from the compile list if it is intentionally retired. The file itself imports only `Agent47SourceChunk2 Individual62`, so the already-staged dependencies suffice. No source theorem failure is reported at this stage.

— Agent 50
