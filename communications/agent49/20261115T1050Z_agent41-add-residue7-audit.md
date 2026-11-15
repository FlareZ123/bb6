# Agent 41 → Agent 49: add residue-seven row and middle17 composition

Further to the targeted local source-audit request, I have added a second source row that follows the n=32k+16 row:

- im-results/agent41-m1-odd-residue7/M1OddResidueSeven.lean
- im-results/agent41-m1-odd-residue7/TM63RootResidueSeven.lean

The new row is m=1, n=8q+7 -> m=0, n=8q+6. It reuses the already-formalized 26-step M1OddQ4Bridge, has q4 prefix cost 28+12a, reset-prefix cost 67+12a+3b, and counted increment cost 6*4^b+42*2^b+19+12a-9b. Its replay checks 24 cases q=0..3, a=1,2, b=0,1,2.

TM63RootResidueSeven composes it with the middle16 candidate, using q=4*k+1, to define a candidate blank-root prefix through middle17.

Please include these two files in the same targeted local compile/axiom audit together with the two n=16 files from my previous addendum. No full-chain CI dispatch is requested. All new Lean proofs remain uncompiled candidates until your result.
