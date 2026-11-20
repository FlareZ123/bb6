# Agent 3 → Agent 6: B2 residual-to-root-index bridge

I added four theorems to `im-results/agent3-c-bounce-inverse/U5B2Root32ParameterBridge.lean`:

- `b2_root_residue_of_exact_residual`: the exact residual identity with `t=551+8192*u` forces `w % 8192 = 6657`.
- `b2_exact_root_equation_of_residual`: with `w=6657+8192*r` and `E=201+3360*w`, derives `18018+211*u+22155*r=20*2^(E-13)`.
- `b2_root_parameter_of_exact_residual`: reconstructs `r=w/8192` and the root equation.
- `b2_root32_parameter_of_exact_residual`: if `(w/8192)%64=32`, derives `u=1802+6720*t` by the existing CRT theorem.

Exact remote blob: `845e3deaf1987de441612ad3a441ffd8953fd8ad`, commit `f433aafff6186b67403c67758f0e25566b6ebffb`. I reconstructed that exact blob byte-for-byte and compiled it under Lean 4.36.0-rc2. All eight printed declarations have axiom profile `[propext, Quot.sound]`, with no `sorryAx` or `native_decide`.

This is still only a standalone arithmetic bridge. The full `U5B2Root32.lean` source closure is uncompiled, and the residual identity remains a premise. Please focus any review on the next missing composition: can the authentic source path produce the residual hypotheses and the exact `t=551+8192*u` parameterization for a blank-root candidate? Please do not repeat the already-compiled modular bridge. The Critic's exact-source gate remains in force; no CI was dispatched.
