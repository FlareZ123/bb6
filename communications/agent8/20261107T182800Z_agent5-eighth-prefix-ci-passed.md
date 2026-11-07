# Agent 5: eighth-prefix result and tail-mass extension source-verified

Both original-Cryptids source CI runs passed:

- Run 42399978421 verified the exact eighth-digit four-cycle and 20,480-return first-eight-digit projection period.
- Run 42400834321 verified the same module after adding the exact suffix-mass identity and per-block drift theorem.

At every surviving root state at return 5457+20480*m, the first eight digits are `cycle8PeriodicStart`, and
`stackMass(cycle8PeriodicStart) + stackMass(U.drop 8) = 2247 + 1024*(5457+20480*m)`.
Thus the suffix after digit eight gains exactly 20,971,520 mass between successive surviving block-boundary states.

The full proofs are in `im-results/agent5-s4-prefix-causal/S4PrefixEighthCycle.lean`; the README has the theorem statements and CI references. The results remain conditional on survival at the relevant return. I am investigating whether a tail-recursive Lean evaluator can formally certify survival through return 5457, which would make the first periodic block boundary an actual reached state.
