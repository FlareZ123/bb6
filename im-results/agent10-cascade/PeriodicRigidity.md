# Periodic reset itineraries: exact arithmetic rigidity

**Scope (2026-11-24):** the three standalone arithmetic Lean modules locally compile with Lean 4.36.0-rc2 and standard axioms only. Their source grammar is an exact copy of FirstInverseComplete.ResetParent. No original-source integration or rooted halt/nonhalt classification is claimed.

Let h be a reset height, k its sweep level, X=2h+5. A successful transition has a>=0 (a=0 for even; a=t+1 for odd with drain exponent t), and

    2^(a+1) X' = 3^a (X + 16*2^k + 2*k + 5).

The exact source band is 4*2^k < h+k+4 and h+k+5 < 8*2^k. Since X' is odd, a+1 is the exact 2-adic valuation of the sum. PeriodicReset.lean proves equivalence with both arms of the standalone Grammar. For a token (a,delta), delta=k'-k>=0. A nonempty word with D=sum(delta), P=2^sum(a+1), R=3^sum(a), G=2^D composes to

    P X' = R X + S*2^k + C*k + E,

with S=16*s, s odd; PeriodicWord.lean proves composition. If this word repeats indefinitely, k_j=k_0+jD. Set Q=(PG-R)(P-R)^2. Necessarily

    Q X_j = S(P-R)^2 2^k_j + C(PG-R)(P-R) k_j
          + (E(P-R)-PCD)(PG-R).

Subtract the right side from the left: the integral residual obeys P Y_(j+1)=R Y_j. Even P, odd R force every Y_j even. Divide the entire sequence by two and repeat; divisibility by all powers of 2 forces zero. Second differences then imply

    PG-R divides S*2^k_j*(G-1)^2.

PeriodicRigidity.lean proves these statements; PeriodicWord.lean lifts them to all nonempty words. Axioms: propext, Classical.choice, Quot.sound only.

## Finite necessary test for fixed positive total level increase D (paper proof)

For an infinite valid periodic itinerary D>0, rigidity gives the limiting slope alpha=S/(PG-R) at each phase; the source band implies 8<=alpha<=16 and hence PG-R>0. Write alpha=16*n/q in lowest terms, n and q odd. Alpha=8 is impossible by parity. If all a=0, any positive delta maps alpha to (alpha+16)/2^(1+delta)<=8, impossible. Otherwise R is divisible by 3, so PG-R is coprime to 3. At cyclic phases P,R,D stay fixed; the normalized phase map

    n'/q = 3^a (n/q+1) / 2^(a+1+delta)

preserves the odd reduced denominator because gcd(n+q,q)=gcd(3,q)=1. If q=1 every phase has alpha=16, which forces 3^a=2^(a+delta), hence a=delta=0, contrary to D>0. Thus q>1, q/2<n<q, gcd(n,q)=1, gcd(q,6)=1, and n odd.

Let w=v2(n+q), m=(n+q)/2^w. Oddness of n' forces w=a+1+delta. There is at most one a in [0,w-1] with q/2<3^a*m<q, since consecutive candidates differ by factor 3. This gives a deterministic finite partial graph on the eligible n for a given q, with edge labels a,delta. The second-difference theorem, after reducing the slope and cancelling powers of 2, requires

    q divides (2^D-1)^2.

For fixed D only finitely many denominators and graph cycles need consideration, independent of reset count and individual valuations. A primitive token period must have a primitive graph cycle of total increment D: repeated graph vertices imply the same subsequent tokens; conversely a shorter token period determines its own unique normalized slope by composition. Surviving graph cycles would additionally require exact affine integrality and source-band inequalities at all phases.

For a complete finite existence/validity test for an individual word, an all-parameter exclusion of periods containing exactly one positive valuation, and the Presburger safety equivalence, see [PresburgerPeriodicity.md](PresburgerPeriodicity.md).

## Exploratory computations (not kernel-checked)

periodic_denominator_scan.cpp enumerates D=1..14, all eligible divisors q of (2^D-1)^2, and graph cycles. No primitive cycle with matching D was found. Graph cycles with differing increments do not qualify.

period_search.py examines 50,000 root reset transitions, searches for two successive equal words of length <=32 and applies the necessary filters. 23,755 candidate occurrences, 242 distinct words, zero surviving. The extra coefficient-denominator condition is necessary: if alpha*2^k+beta*k+gamma is an integer, the reduced odd denominator of alpha divides lcm(den(beta),den(gamma)).

Run with LEAN_PATH set to this directory:
    lean -o PeriodicRigidity.olean PeriodicRigidity.lean
    lean -o PeriodicReset.olean PeriodicReset.lean
    lean -o PeriodicWord.olean PeriodicWord.lean
    g++ -O3 -std=c++20 periodic_denominator_scan.cpp -o periodic_scan
    ./periodic_scan 14
    python3 period_search.py

Next: connect the standalone Grammar to accepted source ResetParent, and investigate unbounded rooted invariants beyond periodic words. Failure to find a periodic itinerary proves neither halting nor nonhalting. The source-certified cutoff of 50,000 from Agent7 remains the actual rooted bound.
