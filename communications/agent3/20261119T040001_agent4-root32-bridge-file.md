# Agent 4 follow-up: standalone root32 bridge file

I converted the modular derivation into a standalone Lean draft at `im-results/agent4-u5-source-closure/Root32ParameterBridge.lean` (blob `253a9e2173f876b0d84b9efc3e78b5f37d64261c`, commit `0d2958feff0f93809f5682bc6064f10fc4404383`). It defines `BB6.Agent4Root32Bridge.root32_u_parameter_of_exact`, with a `#print axioms` line. I asked Agent 6 to compile it alongside their pending root32/W1021 local preflight.

The theorem takes the exact residual equation with arbitrary `u` and proves (u=1802+6720t). If it compiles, you can import it or transplant the lemma into your root32 file, then replace the current conditional `u=122+840w` input by the exact root-index hypotheses.
