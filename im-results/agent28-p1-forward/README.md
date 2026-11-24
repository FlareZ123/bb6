# Exact forward P1 arithmetic return map

The state is (q,v), with v+4 <= q and original odd hub (a,d)=(2(q-v-4),2v+1). Start at (5,0). Define W(q,v) by the first positive t for which 2^t v >= q+t. The result is (q+t,2^t v-q-t). Equivalently iterate v -> 2v mod (q+1), q -> q+1 until the first wrap.

* v >= 3: W(q,v).
* v = 2: W(q,4).
* v = 0: (q+2,q-3).
* v = 1: set x=q-2 and choose unique j with D_j <= x < D_(j+1), where A_j=7*2^j and D_j=A_j-j-7. Let r=x-D_j.
  * r=0: (A_j-1,A_j-6).
  * r=1: W(A_j+j+1,2j+5).
  * r=2: halt.
  * r>=3: W(A_j+r-2,2r-1).

The Lean relation uses first-wrap bits rather than the equivalent exponential expression. The proof includes the G middle exit (two unit steps), the exceptional right-five step, exact closed-form even-phase descent, the secondary reset at residual 1, and source walk concatenation/determinism. Every successful macro strictly increases q. The theorem blank_critical_clock_iff states that the original accelerated source map halts from (2,1) iff this arithmetic orbit reaches (7*2^j-j-3,1) for some j. It is a reduction, not a proof of nonhalting.

Files in dependency order: ForwardUnit, ForwardPhase, ForwardEven, ForwardReset, ForwardHalt. All compiled locally with Lean 4.36.0-rc2 against copied exact definitions; only standard axioms. Original-source CI target forward-unit is pending. The existing ReverseUnitMap of Agent 50 is used for the moving-modulus iteration. This extends it to the complete forward orbit including resets; it does not supersede existing inverse carry certificates.
