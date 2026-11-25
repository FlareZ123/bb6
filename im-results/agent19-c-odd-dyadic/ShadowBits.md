# Compact bit frontier and exact root exclusion

This replaces the cost-word storage in Agent21's DyadicPopulation and the recursive valuation traversal of the older root32 shadow checker by an exact two-kind integer frontier. It is a computational/proof bridge, not a mortality theorem.

For the normalized scalar mass m and numerator x, set b(m)=211 floor(m/2)+108 and N(m,x,d)=x+b(m)+211((m+3d+1) mod 2). Completed node c(m,x) is a genuine positive-cost path at the current accumulated cost n. Pending node p(m,z) is an unfinished last gap of length d>=2 with total intended cost n+1, whose partial quotient z is integral after n bits. The target m already includes the whole intended gap. The following transitions consume one bit:

* c(m,x): if N(m,x,1) is even, emit c(m+4,N(m,x,1)/2); otherwise emit p(m+7,N(m,x,2)/2). Exactly one of these numerators is even.
* Also emit p(m+6,x/2) if n>0 and x is even, extending the last completed gap by two.
* p(m,z): emit c(m,z/2) if z is even; otherwise emit nothing.

The root must not use the last-gap extension at layer zero. There is no need to store words, compute a valuation, evaluate a power of two, or inspect source coordinates in this search. The list semantics permit duplicates; existence rather than multiplicity is what is proved. [ShadowBits.lean](ShadowBits.lean) proves exact membership equivalence (Full or Pending), and the affine transfer from signed OpenAt coordinates, with one additional initial precision bit for mass. [ShadowBitsLift.lean](ShadowBitsLift.lean) establishes that the true source coordinate lift implies the required signed affine equations, and [ShadowBitsExec.lean](ShadowBitsExec.lean) proves that an absorbing-empty tail-recursive evaluator implements the exact frontier. All three compile locally with Lean 4.36.0-rc2, standard axioms only.

[Root32BitsSource.lean](Root32BitsSource.lean) is the proposed direct source adapter: use Agent21's reach_open on the literal RunReach, lift the three normalized affine residuals, and contradict the empty frontier at n, provided n+4<=E-17. The adapter needs original-source CI acceptance. Unlike a fixed-width modular sieve, one can use the actual root-specific budget E-21 and stop as soon as the frontier empties, without materializing any giant power. The missing universal theorem remains that every authentic j actually empties within that budget. This work is stored in im-results because the new executable formulation and its correctness do not close the unbounded root family.
