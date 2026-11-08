# Small-index two-shallow depth-word residue certificates (2026-11-08)

**Status:** Lean 4.36.0-rc2 locally kernel-checked, with matching original-source workflow currently queued. These are **exact arithmetic model** certificates, not yet an unconditional original-source theorem for `14<=n<48`.

The general original-source theorem [SourceOneShallowLift.lean](SourceOneShallowLift.lean) resolves all n>=48 for legal words `2^s (0|1) 2^u (0|1) 2^r`. For the residual range `14<=n<48`, [TwoShallowFiniteBounds.lean](TwoShallowFiniteBounds.lean) now contains three finite kernel-evaluated theorems:

1. `first_overflow_false`: for every n14..47, s0..3 and first shallow type t0/t1, where q=8^s divides both P=2^n and D=14n+92, the exact first shallow *energy numerator* is nonzero modulo `a*512`, with `a=2` for depth zero and `a=4` for depth one. This rules out `u>=3` for actual scalar runs because `a I_after = N1`, and depth-two runs divide I by 8 at each step.
2. `second_overflow_false`: for all same n,s and u0..2, both shallow types, whenever the exact first energy is integral and divisible by `8^u`, the exact second shallow numerator is nonzero modulo `b*512`. This rules out `r>=3` in actual scalar runs.
3. `no_small_bad_test`: no exact two-shallow wall equality among n14..47, s0..3, u0..2, r0..2, and all four shallow-type combinations. This is the exact necessary scalar terminal equality used in [TwoShallowNumeric.lean](TwoShallowNumeric.lean) with the appropriate coefficient tuple `(alpha,C,L,O)` for each shallow type: depth 0 `(1,588,84,232)`, depth 1 `(2,392,56,136)`.

The base critical root's [root_two_prefix_divisor](RootTwoDivisor.lean) already proves `8^s | 14n+92`; since `14n+92<=750<4096=8^4` for n<48, necessarily s<=3. The first and second modular certificates should formally imply u<=2 and r<=2 via the previously verified exact [TwoRunModel.lean](TwoRunModel.lean) energy identity, after which `no_small_bad_test` excludes the terminal wall. **The missing work is to write those three short natural/integer divisibility-to-bound bridges and connect the resulting finite lemma to the unchanged original `inverseAt` source history.** Avoid presenting the finite numerical scan as an original-source theorem until that implication is compiled.

The finite statements are kernel `by decide` theorems, not raw Python scans. Their small bounded parameter domains are explicit and the Lean file uses no `sorry`. A separate Python exploration originally suggested this modular cutoff, but is not needed as proof of these finite statements. Extension to >=3 shallow steps or depths >=3 is untouched.

