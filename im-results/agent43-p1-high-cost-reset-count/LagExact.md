# Exact all-depth lifting of the delayed P1 carry

Status: mathematical proof; Lean source draft, not yet compiled. This is a structural reduction, not a P1 decision or an exact BB(6) result.

Let n ≥ 14 be even, T = 7·2^n, A = T−n−3, and q_i = floor(T B_i / 2^i). In Agent45's existing Trace relation, B_i is the low selected-bit word, a_i the small carry, x_i ∈ {0,1} the next bit, and y_i = q_i mod 2. Its exact edge equations are

    2a_{i+1}+y_i = a_i+x_i(n+i+3),
    2q_{i+1}+y_i = q_i+Tx_i.

Agent45's LagMicro.lean already proves Micro -> Trace. Agent50's earlier legal-gap lifting covers lengths at most n. The following reverse implication needs neither that bound nor a periodicity assumption.

## Theorem

Every Trace n i B a lifts to a Micro n i v w of the original two-counter arithmetic, with v,w strictly positive and uniquely determined by

    v = floor(T B / 2^i)−a,
    w = T−n−i−1−v.

Conversely every positive-length Micro with these endpoint equations is represented by a Trace. Thus the delayed arithmetic abstraction (before source guards) is exact at all depths.

Proof: at i=1 the compulsory bit gives v=w=(T−n−2)/2 > 0. Assume the correspondence at i and write S=v+w=T−n−i−1. Since v,w>0, S≥2. Subtracting the two displayed trace equations gives

    2v' = v+x_i(S−2).
    2w' = w+(1−x_i)(S−2).

Both right sides are positive; the first is even by the two trace equations, and the second is even because their sum equals 2(S−1). The resulting positive integers satisfy precisely the Micro.one or Micro.zero equations and have sum S−1. Induction proves the claim. Uniqueness follows from the quotient and mass identities.

In particular i+n+3≤T, or i≤A, for every Trace. At equality v=w=1, and neither bit can extend it. This rules out *all* infinite delayed traces at fixed n, not merely eventually periodic ones.

A second elementary proof of the cost bound uses the already-established weighted congruence. At m=A+1, D_m(B)−AB−1 = −1−Σ_{j=0}^{A}(A−j)x_j 2^j. It lies in [−(2^{A+1}−A−1),−1], strictly between consecutive multiples of 2^{A+1}. Thus no word at that depth satisfies the congruence. Prefix closure excludes every longer trace. This does not claim novelty for the finite mass bound of Micro itself; the new point is the all-depth reverse lifting of the delayed representation.

## Relevance to P1

The exponential depth bound A is much larger than the practical O(n) cutoff needed by LongConeSource. It does not close an unbounded n family. Moreover Micro is not automatically LegalGap beyond n: one must retain the source guards w≥10 and even at starts and v'≥2,w'≥6 at ends of complete gaps. The exact endpoint map above permits direct tests of those guards without reconstructing a second inverse history. It also separates the actual finite-length problem from infinite-word periodicity arguments.

Lean source: LagExact.lean imports the existing LagMicro and P1CarryExact without modifying them. The local Lean environment is currently unavailable; compilation status must be checked before promoting any theorem to a kernel-certified result.
