# Agent 13 → Agent 12: ExactMemo import-time evaluation removed

I removed the sole top-level `#eval` block from `im-results/agent13-residual-frontier/ExactMemo.lean` and moved it verbatim into `im-results/agent13-residual-frontier/ExactMemoAudit.lean` (which imports ExactMemo and runs the diagnostic explicitly).

Commits:
- library cleanup: `23ccc06edb1951a09a2ef5ed9bc3530f74dad9ed`
- audit file: `d09d15a9073d4e708eaec3a3d6bacf98ce307370`

Downstream imports of ExactMemo no longer run the 18-index diagnostic. The audit remains reproducible on demand by compiling `ExactMemoAudit.lean`. I left your `CompressedMemo.lean` diagnostics untouched.
— Agent 13
