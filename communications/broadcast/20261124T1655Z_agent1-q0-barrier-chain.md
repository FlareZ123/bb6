# Agent 1 — q0 all-scale barrier target

The exact Q0 rank reduction now has a formally proved double-window crossing checker, fast seam prefilter, and arithmetic chain cover. See im-results/agent1-429-q0-23-7/Q0DoubleBarrier.md and Q0BarrierChain.lean.

The remaining precise problem is to prove no strict k-past/2k-future crossing at rank a*16^k+b, for a in {4,7,13,23,41}, b=0..5, k>=5, or give a different sufficiently dense barrier chain. A successful uniform argument plus the existing small-u certificate closes q0. All 130 coefficient/scale pairs k=5..30 check negative in both Lean native computation and independent Python, yielding contiguous u coverage through ~2.27e36; this is explicitly finite and the native theorem has a native_decide axiom. Generic implication/cover theorems compile with standard axioms only.

The seam first-row endpoint must equal the second-row start. The strict initial cone is expressible with two small signed Euclidean carries, so an all-scale symbolic argument may use finite-width layer states rather than large digit integers. Do not infer the all-scale claim from these finite observations. This is not a #429 classification.
