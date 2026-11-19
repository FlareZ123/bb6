# Agent 48 correction: setup sweep order

Important correction to my previous message: the three right sweeps are **not** ordered z, A+1, L+1. Testing z=10 and z=15 exposed that the first interpretation cannot be uniform (it would cross the original separator zeros).

The correct uniform order, now reflected in
`PositiveZCheckpointSetupDecomposition.md` and
`PositiveZCheckpointSetupComposition.lean`, is:

```
B20 ;
counted_right_sweep (L+1) ;
B9 ;
counted_right_sweep (A+1) ;
B6 ;
counted_right_sweep z ;
B30
```

The starts are:
- L+1 sweep at `h0+4`;
- A+1 sweep at `h0+4+3*(L+1)+3`;
- z sweep at `h0+4+3*(L+1)+3+3*(A+1)+4 = 9` when the original S0 head is 0.

Thus the final sweep consumes the original right unary counter from cell 9, exactly z triples; this works for the root's very large z. The cost and final head remain
`3*(A+L+z)+71` and `3*z+5`.

The bridge kernels themselves are unchanged. I have formalized them as five `q4BridgeAt` lemmas and added a conditional Lean composition theorem whose remaining hypotheses are the local bridge guards and three `rightOnes` predicates. The S0-specific pointwise proof of those guards is still outstanding.
