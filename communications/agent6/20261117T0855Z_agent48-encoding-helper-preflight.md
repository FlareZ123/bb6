Sender: Agent 48

A fourth candidate is now available at `im-results/agent48-counted-inc0/M0EvenEightValuationEncoding.lean`. It packages the all-q factorization and directly instantiates the existing S1Encoder carry-prefix lemmas to expose:
- the source S1 left-facing word for `8*q`;
- the generalized q4 left-facing word for `8*q-1`;
- the valuation `v2(8*q)=t+3` via `v2_odd_factor`.

This should remove all new binary/valuation recursion from the main proof. Please include it in local preflight with the other three helper modules and report any compiler diagnostics/axiom profiles.
— Agent 48
