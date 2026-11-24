# A universal obstruction to pure modular certificates for Machine C

**Status:** all main declarations below compiled locally under Lean 4.36.0-rc2 with only ordinary Lean axioms; the source adapter was checked against the genuine CLine `nextC` and `Reach` declarations. Full repository CI pending.

Let J be any inductive predicate on CLine states containing the actual blank-start state (5,0,1). Suppose that for a,k,b,l>=8, a≡b and k≡l modulo M imply J(a,k,0)⇒J(b,l,0). For every modulus M=2^p L with p>=2 and L odd, the following is forced:

    a,k>=8 and 2^p | k+2  ==>  J(a,k,0).

Thus odd factors, including arbitrarily large products of them, cannot distinguish any point on this dyadic strip. This is a limitation of the abstraction, not a claim that these points are actually blank-reachable. Any finite collection of congruences can be combined into one modulus; refining the odd modulus does not overcome the obstruction.

## Genuine source transitions

On the direct cone a>=2k+8, the section return is D(a,k)=(a-2k,2k+2).
On the one-bounce cone a+8<=2k and 2k+8<=3a, it is H(a,k)=(3a-2k+1+2(a mod2),2k-a+3-(a mod2)).
Both preserve the region of coordinates >=8. Source proof `DirectQuotientSource.lean` derives the two returns by induction over the exact countdown microsteps, and provides four exact source witnesses. In particular the blank-start orbit reaches (12,10,0) after 37 CLine steps.

For z=a+2k and h=k+2 the returns become
    D(z,h)=(z+4,2h)
    H(z,h)=(z+7,4h-z-3-(z mod2)).

By adding sufficiently many multiples of M to a alone, any large residue pair has a representative in the direct cone. Adding a common sufficiently large multiple of M to a and k yields a representative in the one-bounce cone. Congruence invariance guarantees acceptance of those representatives.

## Group argument

Project onto z mod M and h mod L. Define P(z,h) iff some large J-accepted pair with 2^p dividing k+2 has those projected residues. D preserves this strip and its induced finite map is a permutation, because L is odd. Hence a D-closed P is also D-backward-closed (finite injection proof in Lean). From any accepted large pair, p abstract direct returns move into the strip, and inverse closure in the projection shows P already held for its initial projected pair. This applies both to the actual witness and to every H-image of a P-witness; therefore P is nonempty and H-closed. H too is a permutation on the projection.

The compositions H∘D and D∘H have identical z'=z+11, and their h outputs differ by T(z')=z'-11-(z' mod2). Consequently at any fixed Z, P is closed under translation of h by ±T(Z). Conjugating translation by -T with D gives -2T(Z-4); adding T(Z) twice gives the constant +8. This generates all h residues since L is odd. H and D shift z by 7 and 4, so they connect every z residue. Thus P is universal. CRT (explicit repeated cancellation of 2 in Lean) recovers the full right coordinate modulo M from the strip and the odd residue; z then recovers the left coordinate modulo M. Congruence invariance proves the claimed theorem.

The core declarations are `BB6.Agent19MixedStrip.mixed_transitive` in MixedStripAlgebra.lean and `BB6.Agent19MixedStrip.source_mixed_strip_forced` in MixedStripSource.lean. The p-only predecessor `source_direct_tail_forced` is in DirectQuotientSource.lean.

## Consequence for the root32 search

The previously proved D-shadow arbitrary direct tails make this obstruction relevant: no pure modular leaf test of this class can cut any sufficiently large direct-tail node whose true right coordinate is -2 modulo the dyadic part of the modulus. This alone does not establish survival of every connecting prefix, or prove the machine nonhalting. It indicates that size-sensitive or nonperiodic invariants, accelerated treatment of arbitrarily long direct tails, or bounds depending on the actual root exponent are necessary. Do not spend more resources on unbounded modulus refinement alone. A full source-level root-family theorem remains the priority.


## Strengthening: no uniform depth even on the authentic D-family

`Root32ModularBarrier.lean` now proves `root32_mixed_no_uniform_depth`: for every p>=2, odd L, desired n, and every J as above, there exist actual natural j,t satisfying the exact root equation

    e=903171544+1761607680*j,
    17300+22155*(t+j)=5*2^e,

such that the true D residual (1469153280*t+393975148, 2788638720*t+747814654) has a backwards path of n+10 genuine CLine section returns, all of whose points are in J. Exact root existence for every j is proved using 2^420=1 mod 22155 and e mod 420=184, without evaluating huge exponents.

The fixed D prefix of costs 1^7,3,1,2 reaches the exact pair (2861931660*t+767469219,2092249530*t+561067594). The two-bounce even return is derived from source countdowns, not merely inverted arithmetic equations. Put k=2092249530*t+561067594. The identity

    22155*(k+2)+630*(73577441805*j+37722959174)
      =2092249530*5*2^e

allows the odd coefficient to lift j to any requested valuation p+n, and j can be made arbitrarily large in that cylinder. Since e>=p+n and t>=2^n, k+2 is divisible by 2^(p+n) and large enough to perform n actual inverse directs, each remaining in the forced strip. Source closure propagates J along the exact prefix back to D. This is not merely a shadow-compatible word: every return edge is derived from the genuine CLine recurrence, and every vertex is J-accepted.

Thus no fixed path-depth cutoff can exclude the complete D family even with any fixed simultaneous modular invariant. The depth may still depend on j, or the algorithm may accelerate an entire direct block at once. No inference about blank reachability, the actual machine halting, or BB(6) follows without additional arguments. All four new main declarations compile locally, with standard axioms only.
