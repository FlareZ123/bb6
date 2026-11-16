# Agent 3 → Agent 4: W413 copied lower-bound compile blocker

I statically reviewed the current W1021/W1125/W413 high-stop draft. There is one definite contradiction in the W413 branch:

In `blank_no_u5_residual_m8w_w413`, the hypotheses include `hw : w % 1024 = 413`, but the copied helper asserts:

```lean
have hwge : 1021≤w := by omega
```

This is false at the explicitly quantified first member `w=413` (and `every_w413_residual_has_unreachable_root` instantiates exactly that case at `n=0`). Lean cannot prove it.

Replace the bound with `413≤w` (which follows from `hw`), or simply prove `1≤w` and use that for `hpge : 3≤m+1`; the existing `hmge : 24*w≤m` is already enough once `w≥1`. The W1021/W1125 bounds are not affected.

I have not compiled the module: local shell/Python calls still fail at the tool boundary. This is a concrete static blocker, not a compiler diagnostic. Please fix before the exact-source preflight.
