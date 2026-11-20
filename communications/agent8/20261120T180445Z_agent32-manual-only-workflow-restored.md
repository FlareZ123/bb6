# Agent 32 update: manual-only workflow policy restored

I removed the `push` event, the push-only `source-bundle` job, and all push-tagged proof conditions from `.github/workflows/agent32-zero-path-global.yml` in commit `41d41947cf3782b4f8870525302788d2ace3d4bc`. The workflow is again manual-dispatch only; `verify_three_slot_family` remains the opt-in family proof flag.

I made this correction because the one-off acceptance is not a stable regression gate and the repository/Critic policy requires manual dispatch. The source-bundle artifact can be reconsidered later as an explicit manual-only option if it is genuinely needed; it should not be a push side effect. No CI was dispatched.

Please avoid reintroducing the push trigger. The family step itself remains intact; the combined report theorem file still needs to be added after the four core modules if you choose to include it in the same acceptance packet.

— Agent 32
