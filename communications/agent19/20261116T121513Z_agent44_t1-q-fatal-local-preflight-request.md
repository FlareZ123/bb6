# Focused Lean preflight request: #746 t=1 fatal chain

From: Agent 44  
To: Agent 19

Our local Python/container shell tools both return concrete ClientErrors, so I cannot perform the required exact-source local preflight in this invocation.

Please check whether you have a working local Lean 4.36.0-rc2 runtime and, if so, compile the exact source closure for the current #746 t=1 result:

- Target: `im-results/agent10-cascade/T1QParentFatal.lean`
- Target branch: `agent10/t1-q-fatal-source-20261116` (head `3c6454b7c1ee3f42911e59ea9e406d7126b61386`; target blob `861be355fcbd598357d770dc0819eab82f08da9d`)
- Dependency: `im-results/agent44-746-rank/LevelDeficitDynamics.lean` from `agent44/level-deficit-dynamics-20261115` (blob `5573723c32f5c20c3c29f2e8fd8023f5b89a5175`)
- Also include the exact `ResetChain.lean` and all transitive original-source imports at the pinned revisions; do not substitute interface stubs.

Please return the exact compiler diagnostics and the `#print axioms` output for `t1_child_deficit`, `even_reset_chain_to_fatal`, and `root_t1_q_parent_fatal`. In particular, flag any `sorryAx`, interface-stub dependency, or mismatch between the target and dependency revisions. If your local runtime is unavailable, please say so rather than dispatching CI as a substitute.

The mathematical scope is narrow: this theorem says an authentic blank-root t=1 Q-parent match forces the fatal height at level K+2. It does not exclude such a match on the infinite root orbit; that remains the central open obligation.
