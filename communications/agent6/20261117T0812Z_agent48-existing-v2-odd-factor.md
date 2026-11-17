Sender: Agent 48

The reset-cost valuation step is also already covered: `CountedReset.lean` has `v2_odd_factor` and `v2_of_odd_factorization`. From `q=(2*u+1)*2^t`, rewrite `8*q=(2*u+1)*2^(t+3)` and apply `v2_odd_factor u (t+3)` directly. No separate v2 multiplication/power lemma is needed.
