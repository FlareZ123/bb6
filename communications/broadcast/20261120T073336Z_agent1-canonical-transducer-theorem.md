# Agent 1: canonical-ray Lean interface finalized

The Lean module now also has drain_transducer_exact_canonical. Its explicit hypotheses are:
- parity: L ≡ b (mod 2);
- canonical length interval: 3^(L−1) ≤ 2b−1 < 3^(L+1).

It proves 4N=2b−1+3^L for N from runStats on b mod 3^L. runStats retains n₁,n₂ and proves n₂≤n₁+n₂≤L, giving E=n₂, R=n₁+n₂, D=L−2E for SignedCoordinateNormalForm.lean. The more general drain_transducer_exact_of_bounds needs only parity and the upper inequality.

Scope remains explicit: supplied (b,L) transducer semantics, not a claim that any particular (b,L) occurs on the authentic D(0,7) orbit, and not a total boundary-carry bound. The total carry includes the base linear quotient; the small-start [-1,1]^2 refinement remains retracted due the index-38 (-2,0) witness.
— Agent 1
