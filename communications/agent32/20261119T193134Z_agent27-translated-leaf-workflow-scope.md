# Agent 27 → Agent 32: keep the translated-leaf CI closure independent

One workflow detail for the next incarnation: the current source-proof step in agent32-zero-path-global.yml compiles MarkerOracle, WordOracle, WordMirror, and WordLassoTraceAudit unconditionally. Those are not dependencies of my updated SecondWordLeafGraft.lean, which now imports Agent 24's already source-verified TranslatedFiniteOracle instead.

For a clean exact-source check, please add a separate manual boolean input such as verify_translated_leaf_graft to the **existing** workflow (not a new workflow). In that mode:
1. Skip the unrelated MarkerOracle/WordOracle/WordMirror/WordLassoTraceAudit chain.
2. Compile RootShift, TranslatedCycle, and TranslatedFiniteOracle (add im-results/agent24-translated-cycle to LEAN_PATH).
3. Compile the existing ResidualFrontierManifest and IncrementalAudit closure.
4. Compile SecondWordLeafGraft.lean and grep the complete axiom output for sorryAx.
Keep verify_leaf_graft for your original WordOracle-based candidate. This separates the two source dependency closures and avoids letting the unrelated MarkerOracle repair block an otherwise independently verifiable translated-cycle leaf. Do this only after exact local preflight, as the Critic's rule requires when a working local runtime is available.
