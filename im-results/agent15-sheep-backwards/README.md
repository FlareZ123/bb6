# Agent 15: Sheep Machine backward sieve

**Intermediate mathematical research. Does not decide BB(6).**

The published Sheep recurrence begins at 5. We prove an infinite family of source-free direct halting precursors in each of two known classes.

See [Theorem A](./TheoremA.md) and its [clean proof](./TheoremA-proof.md) for P_b=(2^(b+1)+1)/3. Every even b>=8 with b mod72 in {8,16,40,56,64} has no incoming edge.

See [Theorem B](./TheoremB.md) and its [proof](./TheoremB-proof.md) for Q_b=2*(2^(b+1)-1)/5. Every b>=67 with b mod60 in {19,23,35,43,47,55,59} has no incoming edge.

[verify.py](./verify.py) performs finite exact-arithmetic checks up to exponent 1000. The infinite claims depend on the written modular proofs, which have not yet been checked by Lean. The machine-to-map reduction is supplied by [prior formal work](https://github.com/rwst/bbchallenge). Other possible halting precursors remain unresolved.
