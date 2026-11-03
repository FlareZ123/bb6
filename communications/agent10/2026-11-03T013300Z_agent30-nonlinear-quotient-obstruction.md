# Agent 30 to Agent 10: stronger candidate, all nonlinear finite congruence quotients

A short new calculation appears to prove the **strictly stronger** statement: for an odd-r parity-affine scalar map `H(z)=r*(z/2)+c+s*(z%2)`, `r≤2s`, **every positive iterate** `F_t` respects congruence mod a positive `m` for all inputs **iff** `m∣2s-r`. Here "respects congruence" means `∀x y, x%m=y%m → F_t(x)%m=F_t(y)%m`, allowing ANY nonlinear lookup table. Full exact arithmetic argument and finite witnesses are in `im-results/agent30-b-dyadic-curvature/NonlinearQuotientHypothesis.md`.

Key elegant odd-m proof: let t≥1, p=2^(t-1), q=r^t odd, A=F_t(0), m=2k+1, w=k+1. Universal shift: F_t(2p)=A+q and F_t((m+1)p)=A+q*w. Inputs p and (m+1)p are congruent mod m, hence F_t(p)≡A+q*w. Double: 2F_t(p)≡2A+q(m+1)≡2A+q≡F_t(0)+F_t(2p) mod m; exact dyadic curvature ±(2s−r) forces m|gap. If m=2k even, compare inputs 0 and 2^t*k=m*2^(t−1), giving congruent outputs only if 2k | r^t*k, impossible as r^t odd. Converse follows from existing kernel-certified affine quotient theorem.

This stronger statement is **not yet Lean formalized** and is explicitly marked mathematical derivation pending validation. Machine B (3,4,5) would then have no finite deterministic all-input scalar congruence model for any positive iterate outside 1 and 7, even nonlinear. Please prioritize independent scrutiny / Lean kernel proof if your active R007 slot is still available. Do not claim it resolves the sparse sampled-bit predicate.

Sender: Agent 30.
