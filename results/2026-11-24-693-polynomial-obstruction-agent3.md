# No eventually periodic itinerary or finite polynomial-congruence safety invariant for #693

**Theorem (Agent 3, 24 November 2026).** Every infinite trajectory of the exact arithmetic acceleration of Cryptid #693 has a non-eventually-periodic branch itinerary and infinitely many accumulation directions. Consequently, no nonempty terminal-free forward-closed subset of the admissible lattice can be specified by a finite Boolean combination of polynomial sign tests and fixed-modulus congruence tests.

This strictly strengthens the prior [semilinear obstruction](2026-11-24-693-semilinear-obstruction-agent3.md). In particular it excludes nonlinear real algebraic curves, finite unions of polynomial regions, and combinations with finite modular partitions as inductive nonhalting certificates in these coordinates. It does not exclude arbitrary arithmetic predicates, and it does not decide the authentic root. The following is a paper proof; the underlying exact coordinate conjugacy and arithmetic acceleration are independently [Lean checked](../im-results/agent3-693-dual/README.md), with the pinned upstream halting equivalence used as an external premise.

## 1. Parity-separated acceleration

For integers E,O>=2, the two terminal gates are E=O and E=O+1. The reset gates are O=E+1, mapping to (3E-1,4), and E=O+2, mapping to (2,3O+1). Outside these gates there are exactly two regular maps:

    T_E(E,O) = (3E,O-E)       if O>=E+2,
    T_O(E,O) = (E-O,3O+1)     if E>=O+3.

Start (3,4), first reset (8,4). Write S=E+O. Each nonterminal step strictly increases S; for regular steps S'=S+min(E,O)+epsilon where epsilon is 0 or 1. Hence

    S'+2 <= (3/2)(S+2).

In a regular interval of length t, S_t+2 <= (3/2)^t(S_0+2).

## 2. Mixed-word matrices have no rational eigenvalue

The linear parts are

    A_E = [[3,0],[-1,1]],     A_O = [[1,-1],[0,3]].

For a mixed word of length k (both letters present), let A be its matrix product, in chronological action order. Its determinant is 3^k. Modulo 3, each factor has rank one, image equal to a coordinate axis, and kernel the diagonal x=y. Any product of these factors is nonzero modulo 3, still has a coordinate axis as image and the diagonal as kernel. It has nonzero trace modulo 3: its restriction to its image is nonzero, since image and kernel are distinct. If A had a rational eigenvalue, it would be an integer root of the monic integral characteristic polynomial; the other eigenvalue would also be an integer. Their product 3^k and sum prime to 3 force at least one eigenvalue to be +1 or -1.

But the inverse factors are

    A_E^-1 = [[1/3,0],[1/3,1]],    A_O^-1 = [[1,1/3],[0,1/3]].

Each is nonexpansive in the vector l1 norm, and preserves the norm of a nonzero vector only if its divided coordinate is zero (E for the first, O for the second). In that case the vector is unchanged. A mixed product of inverse factors therefore strictly decreases the norm of every nonzero vector: equality in the whole product would force equality at each factor and both coordinates zero. An eigenvalue +1 or -1 is impossible. Contradiction.

Thus no mixed word matrix has a rational eigenvalue, and in particular no nonzero integer vector is collinear with its image.

## 3. Quantitative limit on regular-word repetitions

Suppose a regular word of length k occurs m consecutive times, with m>=2, beginning at mass S_0. Write z_j for the state at the beginning of block j (including z_m). All blocks have the same affine map z -> Az+b, so d_j=z_{j+1}-z_j satisfies d_{j+1}=Ad_j. Since S strictly increases, d_0 is nonzero. For a mixed word, section 2 gives the nonzero integer D_0=det(d_0,d_1). Consequently

    |det(d_j,d_{j+1})| = 3^(kj)|D_0| >= 3^(kj).

Also ||d_j||_1 <= S_{(j+1)k}+S_{jk} <= 2(S_0+2)(3/2)^((j+1)k). Apply the determinant bound |det(x,y)| <= ||x||_1 ||y||_1 at j=m-2:

    3^(k(m-2)) <= 4(S_0+2)^2 (3/2)^(k(2m-1)),

or equivalently

    (4/3)^(k(m-2)) <= 4(S_0+2)^2 (3/2)^(3k).

This uniform finite-repetition bound involves the initial mass and word length, not the individual letters of the word. A mixed periodic tail would violate it for arbitrarily large m with fixed k,S_0.

For a pure word of total length L, the repeatedly multiplied counter is at least 3^L times its starting value x>=2, giving 2^L <= (S_0+2)/x. Thus a pure periodic tail is also impossible.

If an infinite itinerary has infinitely many resets, their gaps are unbounded: after a reset one coordinate is 2 or 4 and the other tends to infinity because S tends to infinity. For any fixed L, the first L regular steps after sufficiently late resets must multiply the small coordinate. For example with E=2, E_j=2*3^j and O_j=O-(3^j-1), so for each j<L the even guard holds once O is sufficiently large. With O=4, O_j=(9*3^j-1)/2 and E_j=E-sum_{i<j}O_i, likewise. Therefore the next reset is more than L steps away. An eventually periodic branch word containing a reset would have bounded reset gaps, contradiction. This proves aperiodicity for the full four-branch itinerary of every infinite trajectory.

## 4. Every infinite orbit has infinitely many accumulation directions

Define r=min(E,O)/(E+O) in (0,1/2], and the continuous limiting map on [0,1/2]

    F(r) = min(3r,1-2r)/(1+r).

For a regular even step r'=F(r) exactly. For a regular odd step, the numerator in the new fraction differs from its homogeneous value by at most 1, and the denominator by 1, so |r'-F(r)|<=2/S. For reset inputs, |r-1/2|<=1/S and F(r)<=2/S; their output has min(E',O')<=4 and S'>S, so |r'-F(r)|<=6/S. Since S increases without bound on an infinite orbit, the one-step error tends to zero.

Let Omega be the set of subsequential limits of r_n. Compactness gives nonemptiness. Continuity and vanishing error imply F(Omega)=Omega: forward inclusion follows by taking a subsequence of r_n and its successors; reverse inclusion by taking a subsequence of predecessors of any convergent subsequence with indices tending to infinity.

Suppose Omega were finite. F then permutes Omega. Choose disjoint small neighborhoods around its points so that when r_n is sufficiently near a point x of Omega, r_(n+1) is nearer F(x) than to any other point, using continuity and the positive minimum separation. The distance from r_n to Omega tends to zero, so for all sufficiently large n the nearest-point itinerary follows F exactly and remains in a single cycle. Thus Omega is that cycle.

A cycle containing 1/5 or 1/2 must also contain 0, because F(1/5)=1/2 and F(1/2)=F(0)=0; only the singleton cycle {0} can contain 0. If Omega={0}, eventually r_n<1/10 with S large. There are no gates then, and the smaller counter stays smaller under the regular map (3 min+1 < S-2 min). Hence the actual branch label is eventually constant, contradicting section 3.

For any other finite cycle, all its points are strictly interior and separated from 1/5. Eventually there are no gates and the identity of the smaller counter switches exactly on those phases of the cycle with r>1/5, since the switch condition is 3 min+epsilon > S-2 min. The phase sequence is periodic; the identity of the smaller counter therefore has period the cycle length or twice that length. This makes the regular E/O itinerary eventually periodic, again contradicting section 3.

It follows that Omega is infinite.

## 5. Polynomial-congruence obstruction

Consider a subset C of the admissible integer lattice E,O>=2 specified by a finite Boolean formula whose atoms are polynomial sign/equality tests in E,O with real coefficients and fixed-modulus congruence tests (including polynomial congruences with integral coefficients). Let M be the common multiple of the finitely many moduli. The modular truth values are fixed on each residue pair modulo M.

For every nonzero test polynomial, its highest-degree homogeneous component restricts to a nonzero univariate polynomial on E+O=1 (homogeneity makes identically zero restriction impossible). Its zero set there is finite. Thus there is a finite exceptional set of normalized directions, including the axes and diagonal, outside which every polynomial sign is eventually uniform on sufficiently small closed angular intervals. Indeed the leading homogeneous term is bounded away from zero there, while all lower-degree terms divided by the highest power of S tend uniformly to zero. Identically zero polynomials have constant truth value.

Suppose C is nonempty, forward closed and terminal free. A point in C has an infinite orbit lying in C. By section 4, the unordered direction r has infinitely many accumulation values. Choose a nonexceptional interior accumulation direction, passing to a subsequence with fixed ordering of E,O and fixed residue pair modulo M; this is possible because there are only two orderings and finitely many residues. Around the corresponding ordered direction choose a small open cone with compact angular closure avoiding every exceptional direction. For sufficiently large S all polynomial atoms are constant on that cone, and the congruence atoms are constant on the chosen residue pair. Since arbitrarily large orbit points there belong to C, the entire large cone tail within that residue pair belongs to C.

The previously proved [halting-ray density theorem](2026-11-24-693-semilinear-obstruction-agent3.md#4-halting-rays-in-every-open-cone) states that each such cone tail contains arbitrarily large halting prepared states. The theorem transfers to E,O by the affine bijections E=u,O=v for p=0 and E=v+1,O=u for p=1; the cone is strictly away from the diagonal and axes and thus selects one parity. It maps the fixed residue pair to a fixed residue pair and has a limiting open interior cone in the previous coordinates. Choose a narrower cone in the latter to absorb the bounded shift. A halting prepared state in C contradicts forward closure and terminal avoidance.

Therefore no nonempty C of the stated form exists. The argument also applies to any description having only finitely many exceptional asymptotic directions on finitely many congruence slices, provided truth is constant in every sufficiently narrow cone tail away from those directions.

## Scope

The determinant argument, finite repetition bound, accumulation theorem, and polynomial-congruence obstruction above are mathematical proofs, not Lean-checked theorems in this revision. The coordinate and transition identities are kernel checked in the companion dossier. The earlier density theorem is a paper result with partially checked supporting arithmetic. None of these statements proves that the authentic root is infinite or that BB(6) equals the current champion. They constrain useful root-specific techniques: a successful nonhalting argument in these coordinates must use genuinely non-finite-direction arithmetic, not a periodic itinerary or a finite polynomial/modular safety region.
