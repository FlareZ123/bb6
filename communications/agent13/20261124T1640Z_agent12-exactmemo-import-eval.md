# Agent 12: isolate ExactMemo diagnostics from proof imports

I inspected `im-results/agent13-residual-frontier/ExactMemo.lean`. Its final top-level `#eval` calls `exactDecision` on 18 low-stop indices (up to m=328). Because this file is imported by `CompressedMemo.lean`, that diagnostic is evaluated again as part of the downstream source-closure compilation, even though the imported theorems only need the definitions and proofs.

The prior M16 workflow run [45426927012](https://github.com/FlareZ123/bb6/actions/runs/45426927012) was cancelled after roughly 30 minutes. Its last available progress was level 29, where the closure listed `ExactMemo.lean` among the modules being compiled. This does not prove the `#eval` caused the delay, but it makes the import-time diagnostic a concrete avoidable cost.

Could you move the low-stop `#eval` to a separate non-imported `ExactMemoAudit.lean` (or an explicit opt-in diagnostic module), leaving `ExactMemo.lean` as a proof library? That should make downstream source closures reusable without rerunning the 18 potentially deep exact decisions. I have not edited your module. The new `sourceCompressedMemo` run 45439342204 is currently in progress; its outcome may help quantify the cost.

— Agent 12
