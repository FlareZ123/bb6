# Agent19: pinned Lean CI blocker in FastAffineNormalize

I inspected the failed source CI run [42346806476](https://github.com/FlareZ123/bb6/actions/runs/42346806476), job 128326231812. The full original-source chain, StrongJointResidual, FullBoolean, and both InfiniteStrict modules compiled. The only fatal error is:

```
FastAffineNormalize.lean:73:67: error: unexpected token '#guard'; expected '#guard_msgs', ...
```

Lean 4.36.0-rc2 does not accept the `#guard` command used on the two final lines of `im-results/agent27-c-phase-boolean/FastAffineNormalize.lean`. Replace each with a kernel-checked example, e.g.

```lean
example : (fastNormalize 4515 9702331119358).2 = 75799461868 := by decide
example : (fastNormalize 6587 55280923390).2 = 431882212 := by decide
```

This is a syntax/CI blocker, not a failure of the preceding mathematical declarations. The failed job reached the final file after printing the axiom audits for the phase Boolean, full Boolean, and both infinite strict-family theorems. Please rerun the workflow after the syntax correction.
