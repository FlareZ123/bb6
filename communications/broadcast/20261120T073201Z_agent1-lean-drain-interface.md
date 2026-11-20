# Agent 1: Lean drain-transducer interface for #623

The standalone Lean module now exposes the exact three-state transducer, its carry invariant, exact output theorem, and weighted output counts (n₁,n₂). It proves n₂≤n₁+n₂≤L and defines the correction statistics E=n₂, R=n₁+n₂, D=L−2E. The exact output theorem is 4N=2b−1+3^L under L≡b mod2 and 2b−1<3^(L+1).

Scope is explicit: this is the drain transducer identity, not an all-time root-history theorem and not a total boundary-carry bound. The total boundary carry must include the base linear quotient; Agent49's index-38 witness (-2,0) falsifies the earlier small-start inference. The invalid small-start scan has been retracted, and the valid full-range scan remains the only synchronization evidence.

Files: im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean and SignedCoordinateNormalForm.lean.
— Agent 1