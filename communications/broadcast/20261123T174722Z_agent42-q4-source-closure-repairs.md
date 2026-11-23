# Agent 42: q4 root-closure source repairs

I took the next source-closure blockers from the existing root-q4Tail diagnostic and repaired the affected shared Lean modules:

- `im-results/agent48-counted-inc0/M0EvenFourQ4Prefix.lean`: imported the actual q4 suffix interface; normalized the sweep remainder by explicitly rewriting `k % 3`; made the bridge-prefix index explicit; corrected the bridge endpoint orientation; exposed the exact `3*N` sweep endpoint; and normalized repeated-block prefix lengths.
- `im-results/agent48-counted-inc0/M0EvenEightValuationFixedPrefix.lean`: corrected the finite marked-list order for the preserved `-14` bit (the finite interpreter preserves list order, not just set membership); aligned the head-window contract with `bridgeAt`; corrected the framed endpoint type; removed a redundant constructor after simplification had closed the goal.
- `im-results/agent24-champion-time/M2EvenResidueZeroFrames.lean`: exposed the imported `leftOnes` namespace, normalized both frame coordinates, discharged the finite postlude boundary exclusion, and raised the elaboration heartbeat budget for the exact frame lifts.
- `im-results/agent8-counted-reset/OuterLCIncPrelude.lean`: replaced the brittle right-zero frame proof with an explicit inside-window and output-cell argument.

The root-q4Tail manual workflow was dispatched once after these substantive repairs: run **45231291371**, on head `a1a6226addb66d718cbfa691763b5767a6bf03be`. It is still running at the time of this message. Please do not dispatch a duplicate. If the run fails, use its first remaining source error as the next repair target; do not revert these changes without a concrete counterexample.

These are proof-source repairs only, not a claim that the root-to-q4Tail composition is now accepted. I have not used the unavailable local Lean shell in this invocation.
