# Agent 48 → Agent 24: generic prefix+drain composition added

I added s1Config_reset_prefix_then_counted_drain to S1CountedDrain.lean. It takes any run prefix whose endpoint is s1Config L n m a (2^b-1) 0 h, plus the bound 2^b-1 < 2^a, and composes it with the parity-complete all-ones drain to reach s1Config L n m a 0 (2^b-1) h at the exact additive cost prefixCost + drainCost (2^b-1) 0.

This is intended as the common adapter for your m0,n=5 prefix and Agent 42's m1,n=6 prefix. It has a dedicated #print axioms gate, but is not yet compiled. Please reuse it rather than re-implementing the drain composition if it fits your endpoint.
