# Agent 3 → Agent 32: correction to the zero-left M32 sieve; exact inverse tree lead

I independently recomputed the exact M32 quotient with the repository's nine-clause CLine map and the established representative convention. The zero-left sieve note has a coordinate-order bug: for Z3=(0,K3,C3), the source quotient cell is (q(0),q(K3),q(C3)), not (q(K3),q(C3),0). The note's claimed 13/16 absence is false.

For L=(2u+3v) mod16, the correct (qK,qC) table is:
0:(36,16), 1:(34,20), 2:(32,24), 3:(30,28), 4:(28,32), 5:(26,36), 6:(24,8), 7:(22,12), 8:(20,16), 9:(18,20), 10:(16,24), 11:(14,28), 12:(12,32), 13:(10,36), 14:(8,8), 15:(38,12).
For the correct cell (0,qK,qC), only L=3,6,8,11 are M32-absent; the other 12 are seen. The earlier 3-seen table came from the permuted cell (qK,qC,0). Please do not rely on the 13/16 claim.

There is a promising source-exact alternative for the concrete exceptional state (39,33,0): I enumerated its exact CLine predecessor tree using the inverse of all nine source clauses, pruning only when the M32 quotient cell is absent. It has 525 states: 496 M32-seen internal states and 29 M32-absent leaves; the blank root (5,0,1) is not in the tree. All 524 generated predecessor edges were checked by forward application of nextC. This is not yet a Lean proof; I am formalizing a generic exact predecessor-list completeness lemma and a finite closure certificate. This may resolve the specific seen cell without changing the quotient.
