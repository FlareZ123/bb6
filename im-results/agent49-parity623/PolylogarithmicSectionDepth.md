# Uniform polylogarithmic section depth for #623

**Theorem.** Every successful chain of k original #623 section transitions, starting at any positive-mass state and ending at D(x,y) with x+y < 2^N, satisfies

    k <= 4 N^2 + 5 N.

In particular, the genuine blank section orbit from D(0,7) has at most O(N^2) visits below a mass cutoff of N bits. This gives a polynomial-time decision procedure for reaching any specified section state, or a bounded family with an efficient membership predicate. It is a conditional growth/finite-target decision theorem, not a whole-machine halting or nonhalting proof. The bound implies exp(Omega(sqrt(k))) mass growth on any infinite successful chain with positive initial mass, improving the prior uniform additive growth guarantees.

## Exact two-scale transition lemma

For every successful drain B(A,b,z)=D(x,y), including visits to zero first budget,

    A <= x+b,    z+3b <= y,    A+z+3b <= x+y.

These follow by induction on b using the five successful flat recursion cases. The child b is strictly smaller. The potential A+z+3b increases respectively by 1,3,1,1 on residues 0,1,2 with positive budget and residue 2 with zero budget (residue 0 also at A=0). The third potential z+3b increases by 0,4,2,1. The first coordinate can decrease at most one per step, and at most b steps occur.

Write s=a+d, m=min(a,d), s'=x+y and m'=min(x,y). Apply the drain bounds to the exhaustive six-branch partition in [InverseWindowSource.lean](InverseWindowSource.lean), now factored as ParentEnvelope P so it can share the original branch derivation with the inverse proof. The exact offsets yield

    s' >= s+m+4
    s >= 5m+9  =>  m' >= 2m+1.

For example, far-left odd has A=a-d-5, b=d+3, z=5, so s'>=a+2d+9 and x>=a-2d-8=s-3m-8; y>=3d+14. Under the stated imbalance, both x and y are at least 2m+1. The far-left even branch has smaller offsets; the right branches satisfy the same inequalities from the corresponding A,b,z reconstruction. The diagonal exception cannot meet the imbalance premise. Both exact axis formulas also satisfy the lemma. The complete split, including odd first counters which return successfully, is kernel checked in [MassBandSource.lean](MassBandSource.lean), theorem next_two_scale.

## Length bound

Classify a step as big if s < 5m+9, small otherwise. For a big step s <= 5m+8 <= 5(m+4), so 5s' >= 6s. For a small step m'+1 >= 2(m+1). Every step is mass increasing.

If the entire chain ends below 2^N, every intermediate mass is below 2^N. If b big steps occur, monotonicity gives 6^b s_initial <= 5^b s_final. Since s_initial >= 1 and 6^4 > 2*5^4, b < 4N. A contiguous run of r small steps satisfies 2^r <= m_final+1 <= 2^N, hence r<=N. Thus k <= b(N+1)+N <= 4N^2+5N. The generic integer proof is kernel checked in [MassBandArithmetic.lean](MassBandArithmetic.lean), without assumptions about a specific machine or approximate logarithms.

The source adapter chain_path transfers the two-scale lemma into that generic Path type, and chain_length gives the claimed bound. root_target_iff proves, for x+y<2^N,

    (exists k, rootRun k = some (D x y))
      iff (exists k <= 4*N*N+5*N, rootRun k = some (D x y)).

Here rootRun iterates the imported highLevelNext from D(0,7), the same genuine root identified by the original source acceleration and Parity623Source.run_eq_highLevel_iterate.

## Algorithmic consequence

For target mass cap C>0 set N=bit_length(C). Iterate the exact source section map from D(0,7), testing states while their mass is <=C; stop at failure or the first larger mass. By strict mass growth there are no later targets, and the theorem bounds the number of live tests by 4N^2+5N+1. Each exact flat drain uses O(N) constant-divisor big-integer arithmetic operations while mass <=C, so the entire process requires O(N^3) such arithmetic operations, or O(N^4) elementary bit operations with ordinary linear-time fixed-small-divisor arithmetic. A successful step crossing the cap has O(N) output bit length by the flat bounds, and a failed step also terminates its drain in O(N) operations. A bounded family does not need to be enumerated: apply its membership test to those O(N^2) actual root visits. This replaces a mass-linear worst-case horizon by a provable bit-length-polynomial one.

The theorem does not give a common finite cutoff for an unbounded terminal family. The previous 20,000-step simulation is not repeated here. The useful remaining target is an all-time root restriction, possibly by proving that the bounded-family certificates share a uniform symbolic mechanism.

## Verification scope

MassBandArithmetic and MassBandSource compiled locally under Lean 4.36.0-rc2; the latter used the definition-identical pinned source excerpt and the exact prior flat-equation module. All printed exported theorem axioms were standard [propext, Classical.choice, Quot.sound]. The existing manual flat-drain workflow is wired to compile them against the complete unmodified upstream module. No new full-source run has been observed. The generic envelope refactor preserves the prior inverse theorem's statement and shares one exhaustive branch proof.
