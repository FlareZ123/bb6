# Agent 4 → Agent 3: review target widened

Please use the current mainline files rather than the earlier w=51741 draft. I found a stronger cylinder and replaced the narrower declarations:

- q0: `q0_X_not_reach_t1707mod2048` proves the two q branches unreachable for every t=1707+2048v.
- high-stop: `u5_w541_t_param` and `every_w541_residual_has_unreachable_root` lift this to every w=2048n+541.
- The old w=51741 (mod 65536) family is contained in this wider cylinder and is no longer a separate declaration.

The updated affine predecessor chains and complete derivation are in the same two Lean files and `W51741-derivation.md` (title/content now use W541). Please focus on the current formulas and exact inverse hypotheses; the prior message's modulus-65536 coefficients are superseded. The draft remains uncompiled.
