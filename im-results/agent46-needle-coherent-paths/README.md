# Space Needle: coherent modular path completeness and the periodicity obstruction

**Status:** six locally compiled Lean 4.36.0-rc2 modules, only standard axioms. Exact shifted-counter arithmetic, using the existing [source equivalence](../agent48-space-needle/SpaceNeedleClosed.lean); unchanged upstream source has not been imported in this new bundle. No blank-root decision, BB(6) bound, or external novelty assertion.

## Main theorem

Write b=d+2. The exact legal edge is

    p = 2^v(2q+3),  c = p+v+3(q+1),  v,q >= 0.

For every odd M>0, h>=0, residues r,s modulo P=2^h M, and lower bound N, there exists a single genuine path of **exactly h+1 successful edges** starting at p>=N with p=r (mod P) and ending at c=s (mod P).

This is coherent path completeness, not a claim about concatenating independently witnessed quotient edges. In particular the true dyadic valuation condition is retained at every step. It strengthens Agent48's [odd-modulus relaxed surjectivity](../agent48-space-needle/MODULAR-ABSTRACTION.md) to mixed moduli and actual paths. The witness start depends on the prescribed endpoints; the theorem does not imply the authentic blank start visits all residues.

### Exact word transport

For a fixed finite valuation word w=(v_1,...,v_t), put S=sum(v_i+1), L=product(2^(v_i+1)+3). The exact arithmetic path relation records the word. From any legal w-path p -> c, all its translations

    p+2^S u -> c+L u, u>=0

are legal paths with the identical word. For any two paths of the same word,

    2^S(c'-c) = L(p'-p).

Since L is odd, 2^S divides p'-p. Thus any realized word occupies a unique dyadic cylinder, and all sufficiently large points of that cylinder realize the word.

### One-edge mixed lifting

For any odd A>0, arbitrary odd-modulus source and target residues a,b, any target residue z modulo 2^h, and arbitrary lower bounds on v and q, there is a legal edge satisfying all those requirements. First use the general theorem that v+B*u^v+C is surjective modulo A for any unit u, with v arbitrarily large. Proof: choose a positive unit period e<A by pigeonhole; apply strong induction modulo gcd(e,A), then solve the linear shift by e using Bezout. This is a formal generalization of the argument in Agent48's modular-abstraction note. With u=(A+1)/2, the target odd residue is determined by

    c = a+v+3u*a*u^v-3u (mod A).

Choose v accordingly. For this v, the source equation gives one linear congruence on q modulo A with coefficient 2^(v+1), and the target dyadic residue gives another with odd coefficient 2^(v+1)+3. Both are solvable; CRT combines them, with q arbitrarily large. This constructs the exact edge rather than dropping the valuation condition.

### Coherence

Every class modulo P has a legal finite path of any prescribed length t: start large in that class, and extend the path after a translation by u=P*j. The new endpoint runs through a positive-step arithmetic progression, which cannot consist entirely of powers of two (two sufficiently large consecutive progression terms have ratio strictly between 1 and 2). Hence some endpoint admits the next legal edge.

Choose such a path of h edges. Its S>=h. Its translations with u=M*j retain the initial residue modulo P, and their endpoints are c+LM*j, an arithmetic progression of odd step A=LM. Apply one-edge mixed lifting to this odd modulus A, choosing the next source congruent to c mod A and sufficiently large to be on that progression, and choosing the final output congruent to s modulo A and 2^h. It is therefore congruent to s modulo P. The translated prefix and final edge are one exact path.

## Consequence: no eventually periodic unary inductive power-free set

Suppose I is a subset of positive counters, closed under all exact legal edges, whose membership above threshold T depends only on the residue modulo some P>0. If I contains any member above T, coherence implies it contains every integer above T. In particular, if I contains a positive starting counter and excludes every power of two, it cannot be ultimately periodic: every nonpower has a legal strictly increasing edge, so closure ensures arbitrarily large members, contradicting the cofinite conclusion. This excludes the unary fixed-modulus/ultimately periodic certificate approach even with exact valuation coupling. It does not exclude nonperiodic, tape-dependent or history-sensitive invariants.

## Consequence: valuation itineraries cannot be ultimately periodic

If a nonempty word w is repeated r+1 times in consecutive blocks on a genuine orbit x_0,...,x_(r+1), the delta identity yields

    2^(S*r)(x_(r+1)-x_r)=L^r(x_1-x_0).

Coprimality and positive drift give 2^(S*r) | (x_1-x_0) and therefore 2^(S*r)<=x_1-x_0. Thus no fixed nonempty valuation word can repeat infinitely. This applies from any prepared positive start, and excludes ultimately periodic valuations on any infinite blank-start orbit. It does not exclude arbitrary aperiodic infinite trajectories, or other kinds of acceleration.

## Reproduce

Use Lean 4.36.0-rc2, b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a. In this directory:

    export LEAN_PATH="$PWD"
    lean -o NeedleCongruence.olean NeedleCongruence.lean
    lean -o NeedlePeriod.olean NeedlePeriod.lean
    lean -o NeedleWord.olean NeedleWord.lean
    lean -o NeedleMixed.olean NeedleMixed.lean
    lean -o NeedleCoherent.olean NeedleCoherent.lean
    lean NeedleInvariant.lean

All six modules passed locally. The principal audited theorems affine_exponential_surjective, path_transport, path_delta, cylinder_unique, repetition_bound, no_infinite_repetition, mixed_edge, coherent_classes, cofinite and no_periodic_power_free list only [propext, Classical.choice, Quot.sound]. No sorryAx, native_decide, finite test substitution or extra assumptions. The word-level theorem is stated for the exact arithmetic edge, not the original imported machine. The existing source correspondence highLevelNext_iff_oddTower plus oddTower_factor identifies that edge with shifted original high-level transitions.

The next missing mathematical step remains a genuine root-sensitive invariant or a halting witness; further relaxed residue catalogs are ruled out as a complete approach.