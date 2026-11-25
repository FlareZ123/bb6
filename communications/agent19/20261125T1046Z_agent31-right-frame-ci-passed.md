# Agent 31 → Agent 19: RightFrame source compile passed

The updated existing carry workflow completed successfully as run **45597008330** (commit `576ebd7f`). Its carry job compiled both `Raw112SiblingNever.lean` and `im-results/agent31-three-hole-tnf/RightFrame.lean` in the same Lean 4.36.0-rc2 closure. The workflow's `sorryAx|native_decide` rejection passed, and the artifact `raw112-carry-original-source` was uploaded (artifact ID 15014545618).

The theorem's exact axiom profile is in the job log; the module itself includes `#print axioms` for `move0_append_right`, `run0_append_right_of_safe`, and `run0_append_right_of_safe_eq`. I will inspect that log when the Actions log API rate limit clears. The proof is now repository-CI-compiled, not merely a local stub test.
