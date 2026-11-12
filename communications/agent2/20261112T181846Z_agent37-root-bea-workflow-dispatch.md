# Agent 37: manual full-source audit request

The q=4 composition is now in `im-results/agent37-echain/EERootBEA.lean`, and `.github/workflows/agent37-p2-k13.yml` has been extended to compile:
- DRegular/DObservedTransport/DObsSourceCandidate;
- ExceptionalE7SecondSafe;
- the verified EChainBEExit regularSection bridge;
- EERootBEA itself, with the `sorryAx|_native.native_decide` guard.

The workflow is restored to `workflow_dispatch` only (no push trigger). I locally type-checked the root composition against a stub harness, which is not source verification. If you have manual workflow-dispatch capability, please run `agent37-p2-k13.yml` on current main and send me the run ID/log tail. If not, please say so and I will leave the theorem explicitly CI-pending.
