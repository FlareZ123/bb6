# Semialgebraic and algebraic-curve obstructions for machine #623

**Agent 49, 2026-11-24. Paper theorem derived from the exact source reduction; new argument not yet kernel checked.**

## Theorems

**Theorem A (algebraic curves).** No tail of any infinite successful orbit is contained in a nonzero real polynomial zero locus, even with arbitrary real coefficients. Thus every such tail is Zariski dense in the real affine plane.

**Theorem B (all semialgebraic sets with fixed congruences).** There is no nonempty safe inductive set Q of the form

    Q = union over residues ρ mod M of (S_ρ ∩ {v in N² : v ≡ ρ mod M}),

where M is a positive integer and every S_ρ is real semialgebraic, with arbitrary real polynomial coefficients. Safety means every T(v) succeeds and belongs to Q for v in Q. This includes arbitrary finite Boolean combinations of polynomial equalities and inequalities and fixed congruence tests on the two counters. In particular it contains the earlier semilinear/Presburger obstruction. Theorem B does not exclude variable-modulus tests, digit/history predicates, or genuinely nonsemialgebraic invariants.

### Proof of Theorem A for algebraic coefficients

Let T denote the certified accelerated transition on section states D(a,d) of machine #623, defined in the pinned [Cryptids source c86f1586](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). No infinite successful orbit of T, from any initial section state, is eventually contained in the zero locus of a nonzero polynomial P(a,d) with real algebraic coefficients.

Consequently no finite union of such algebraic curves can be a safe inductive invariant for the blank-origin section D(0,7), even with arbitrary extra congruence restrictions. Unlike the [semilinear obstruction](NoRegularInvariant.md), this rules out exact polynomial equalities of arbitrary degree, including Pell-type relations. The proof in sections 1–5 initially treats algebraic coefficients; section 6 removes this restriction. It does not exclude infinitely many intermittent visits to a curve.

## 1. Exact correction facts

Write v=(a,d)^t, s=a+d and H(v)=(|a-d|,3 min(a,d))^t. The source theorem next_strict_mass in [Parity623Source.lean](Parity623Source.lean) gives s'≥s+7 on every successful transition.

The flat-drain identities in [FlatDrainSource.lean](FlatDrainSource.lean) (source CI 42526275080) give T(v)=H(v)+e(v), with both signed integer components of e bounded by C log(s+2) uniformly. Indeed, in a successful drain B(A,b,z), each nonterminal step sends block count b=3q+r to q−1, q, q+1 for residues 0,1,2 respectively, except that residue 2 at A=0 uses q. Each step changes the first counter by at most 1 and increases z+3b by 0,4,2,1 respectively. The block count decreases at least by a factor of two for b≥2, and a successful step at b=1 reaches zero. Thus the drain length is O(log(b+2)). The stated uniform estimate follows from the source branches, including the a=0 and diagonal exceptions.

We need the stronger conclusion that along any successful sequence of states with s→∞ and a/s bounded away from 0,1/2,1, the error vectors e(v) cannot remain bounded. Eventually each such input uses one of the four drains below:

| Branch | A | b | z | α | β |
|---|---|---|---|---:|---:|
| a>d, odd d | a−d−5 | d+3 | 5 | −5 | 14 |
| a>d, even d | a−d−2 | d+2 | 2 | −2 | 8 |
| a<d, odd d | d+4−a | a−1 | 3 | 4 | 0 |
| a<d, even d | d+1−a | a+1 | 0 | 1 | 3 |

The final row bundles the initial evalA into a drain by unfolding its positive block-count case; the recursive decrease guard is redundant by the source index bound, as in [FatalDiagonalSource.lean](FatalDiagonalSource.lean).

The initial A grows at least linearly in s, and b→∞. Hence eventually all first counters during each drain are positive. If N_r counts the flat steps at residue r, telescoping gives

    e₁ = α + N₀ − N₁ − N₂,
    e₂ = β + 4N₁ + 2N₂.

Moreover L=N₀+N₁+N₂→∞: each reverse step satisfies b≤3b'+3, so b≤3(3^L−1)/2 at the beginning of a length-L drain. Since β≥0,

    L = e₁−α+2(N₁+N₂) ≤ |e₁|+|α|+e₂.

In particular the two integer errors cannot both remain bounded.

## 2. An algebraic curve forces a periodic limiting direction

Suppose an infinite successful orbit v_n eventually satisfies P(v_n)=0. Its masses s_n→∞. Let x_n=a_n/s_n. Divide the polynomial identity by s_n^m, where m is the total degree. A nonzero constant polynomial is immediately impossible. Otherwise every accumulation point of x_n is a zero of the nonzero univariate polynomial P_m(x,1−x), where P_m is the leading homogeneous part. Nonzeroness follows from homogeneity: vanishing identically would imply P_m(a,d)=0 throughout the positive quadrant.

Let S be the actual nonempty finite set of accumulation points. The normalized leading map is

    g(x) = (1−2x)/(1+x)   if x≤1/2,
           (2x−1)/(2−x)   if x≥1/2.

The uniform error estimate implies x_(n+1)=g(x_n)+O(log(s_n+2)/s_n), so g(S)⊂S. Compactness also gives dist(x_n,S)→0. For all sufficiently large n, the nearest label in S is unique, and continuity of g plus the vanishing error ensures the next label is its image under g: distinct labels have a fixed positive separation. Hence the labels are eventually periodic. Since every element of S is a subsequential limit, S is exactly one cycle.

The only cycle meeting 0,1/2,1 is the singleton {1}, since g(1/2)=0 and g(0)=g(1)=1. This is impossible for an actual infinite orbit. If x_n→1, eventually a_n≥d_n+5. The two far-left formulas then give d_(n+1)≥3d_n+8, while a_(n+1)≤a_n−d_n+O(log(d_n+2)), using the drain length bound in terms of b=d_n+O(1). Eventually d_n→∞ and a_(n+1)<a_n, impossible for natural counters.

Every point of the remaining interior cycle is irrational. As in the semilinear obstruction, represent a rational interior slope by a primitive positive integer pair. Off the diagonal the gcd of its image under H is either 1 or 3. Whenever it is 3, division to a primitive pair strictly decreases mass, so these steps cannot continue forever. At the first gcd-1 step the first output is nonzero modulo 3 and the second is zero modulo 3. This pattern is preserved forever, so subsequent gcds are 1 and masses strictly increase. There is no interior rational cycle. The cycle points are algebraic because they are zeros of P_m(x,1−x).

## 3. The transverse deviation is logarithmic

For each phase i in the cycle of length p write r_i=x_i*/(1−x_i*), a positive irrational algebraic ratio. Define w_n=a_n−r_i d_n on phase i. Eventually actual and phase directions agree on the side of the diagonal. The leading matrices are

    H_L = [[1,−1],[0,3]],     H_R = [[−1,1],[3,0]].

The p-step product M_i has positive eigenvector (r_i,1)^t with eigenvalue λ equal to the product of the cycle mass factors. Each factor is 1+min(x_i*,1−x_i*) in (1,3/2], so 1<λ≤(3/2)^p. The other eigenvalue μ=det(M_i)/λ satisfies |μ|≥2^p. The transverse covector (1,−r_i) is a left eigenvector with eigenvalue μ: it annihilates the first eigenline, its one-dimensional row space is preserved, and the eigenvalues are distinct.

At indices separated by p in the same phase, write W_k=w_(n₀+kp) and S_k=s_(n₀+kp). Composition gives

    W_(k+1)=μ W_k+E_k,    |E_k|≤C_p log(S_k+2).

The matrices and period are fixed; at large indices the one-step mass is at most 7s/4 by the uniform error estimate. Thus S_(k+j)≤(7/4)^(pj) S_k. Since |W_(k+j)|≤C S_(k+j) and (7/4)^p<|μ|, backwards iteration and passage to the limit give the absolutely convergent identity

    W_k = −Σ_(j≥0) μ^(−j−1) E_(k+j).

The geometric mass bound gives W_k=O(log(S_k+2)). Across finitely many phases, w_n=O(log(s_n+2))=O(log(d_n+2)), as all phase ratios are finite and positive.

## 4. The polynomial equation makes the deviation algebraically rigid

Fix a phase with ratio r. Make the invertible substitution a=rd+w and collect powers of d:

    P(rd+w,d)=Σ_(j=0)^J d^j Q_j(w),     Q_J nonzero.

The Q_j have algebraic coefficients. Dividing by d^J and using w=O(log d) gives |Q_J(w)|=O(d^(−1)(1+log d)^m)→0 for J>0; for J=0, Q_0(w)=0 exactly. A nonzero constant Q_J is impossible. A nonconstant polynomial grows in absolute value as |w|→∞, so w stays bounded. Reapply the divided equation with this bound to get |Q_J(w)|=O(1/d). Factoring Q_J, the distance to its nearest complex root is O(d^(−1/deg Q_J)); nonreal roots have fixed positive distance from the real line and are eventually excluded.

Thus, uniformly over the finitely many phases, there is ε>0 such that

    w_n=c_n+O(s_n^(−ε)),

where c_n belongs to a fixed finite set of real algebraic numbers for that phase. The c_n need not be periodic.

## 5. Integer drain corrections contradict the rigid deviation

Across a phase transition r→r', there is a nonzero algebraic scalar t with (1,−r')H_L/R=t(1,−r): the left side annihilates (r,1)^t and the matrix is invertible. Hence

    w_(n+1)=t w_n+e₁(v_n)−r'e₂(v_n).

Substitute the approximations from section 4, using mass monotonicity:

    |e₁−r'e₂−(c_(n+1)−tc_n)|=O(s_n^(−ε)).

For any fixed phase and choices c,c', take a number field K containing r',t,c,c'. Choose a positive integer D clearing denominators of these algebraic numbers and their products in the ring of integers. If z=D(e₁−r'e₂−c'+tc) is nonzero, it is a nonzero algebraic integer; its field norm is a nonzero integer. All conjugates other than the chosen real embedding are O(1+log(s_n+2)) by section 1. Therefore

    |e₁−r'e₂−c'+tc| ≥ C_K (1+log(s_n+2))^(−([K:Q]−1)).

Constants can be chosen uniformly over the finite phase/root choices. A negative power of s_n eventually falls below this lower bound, so for all sufficiently large n the exact equality e₁−r'e₂=c_(n+1)−tc_n holds.

Because r' is irrational, each fixed right-hand side admits at most one integer pair (e₁,e₂). The finitely many phase/root choices force both integer errors to remain bounded. This contradicts section 1 and completes the proof.

A finite union of polynomial zero loci is the zero locus of their nonzero product. Any safe inductive invariant restricted to such a union would force an infinite orbit contained therein.

## 6. Arbitrary real polynomial coefficients

For any fixed finite degree, evaluate the monomials at all integer points in the hypothetical orbit tail. The resulting rows have rational entries. Their row span over Q has a finite rational basis drawn from those rows. If a nonzero real coefficient vector annihilates every row, the row rank is strictly below the number of monomials, hence the rational nullspace is nonzero as well (Gaussian elimination over Q). A nonzero rational polynomial vanishes on exactly that tail, contradicting sections 1–5. This proves Theorem A with arbitrary real coefficients, and therefore excludes any finite union of real algebraic curves.

## 7. A zero-transverse-charge pumping lemma

This is the additional arithmetic needed for Theorem B. Write J(b)=N₀−N₁−N₂ and E(b)=4N₁+2N₂ for the unconstrained positive-budget flat word of b; their exact recursive definitions, trace correspondence and positivity budget have kernel checks in [DrainCorrectionGrowth.lean](DrainCorrectionGrowth.lean). Every inverse digit acts on the remaining positive block count c by

    L₀(c)=3c+3, L₁(c)=3c+1, L₂(c)=3c−1.

For c≥1 these are strictly increasing above c, have distinct residues, and prepend precisely their indicated digit to the complete flat word of c. A finite word w acts by composition L_w(c)=3^length(w)c+C_w; digit counts and J,E are additive.

**Pumping lemma.** For positive integers p,q and any arithmetic progression b=b₀+M t, M>0, there exist a constant K and arbitrarily large members b of the progression with qJ(b)−pE(b)=K.

Proof: factor M=3^v m with gcd(3,m)=1. Pick a member b* sufficiently large that its first v unconstrained flat digits exist and leave a positive tail c. Let w be their prefix, so b*=L_w(c). Such a member exists since after j steps the remaining count is at least b*/3^j−3/2. Let u consist of q+4p copies of digit 0 followed by q copies of digit 1. Its charge is

    q J(u) − p E(u) = q·4p − p·4q = 0.

As multiplication by 3^length(u) is invertible mod m, L_u induces a permutation of the m residue classes. There is a positive N for which L_u^N fixes c mod m. Then b_n=L_w(L_u^(Nn)(c)) tends to infinity, equals b* mod 3^v and mod m, and thus belongs to the progression for every sufficiently large n. Its total transverse charge equals that of b* by additivity. QED.

The proof does not claim that these pumped b values are blank reachable. They will be used only to test any purported inductive set that is required to contain an entire arithmetic ray.

## 8. Rational ray propagation and the infinite-direction case

Suppose a safe congruence-semialgebraic Q contains an arithmetic ray

    (a,d)=(a₀+P t,d₀+R t),    t≥0,

with P,R positive integers and P≠R. Restrict t to a tail of one parity progression, fixing both coordinate parities. For large t, the ray lies strictly on one side of the diagonal and uses one of the four section 1 branches. If it uses the direct odd-a halt branch this immediately contradicts safety. Otherwise A,b are affine in t with strictly positive linear coefficients and z fixed. Consequently all sufficiently large t give positive-budget traces: A grows linearly in b and the flat length is O(log b).

The leading output direction has positive rational ratio p/q=|P−R|/(3 min(P,R)), in lowest terms. The exact transverse output coordinate satisfies

    q a'−p d' = q|a−d|−3p min(a,d)+qα−pβ+qJ(b)−pE(b).

The first four terms are constant on this ray. The b values themselves form an arithmetic progression. Section 7 supplies an unbounded subsequence with constant last two terms, so T maps these inputs to infinitely many points on a fixed rational-direction line q a'−p d'=C. All those outputs belong to Q. Restrict to a residue class of Q containing infinitely many such points. The restriction of its real semialgebraic region to that real line is a one-variable semialgebraic set, hence a finite union of intervals and points. Unboundedness in the positive direction forces inclusion of an entire line tail. Its natural lattice points in the given residue class contain a complete arithmetic ray of direction (p,q). Thus Q contains a ray whose direction is exactly the leading image of the original ray. This propagates rays, without assuming a complete forward affine formula for all parameters.

Let S be the actual limit set of normalized slopes x=a/(a+d) along points of Q of mass tending to infinity. The set is nonempty by strict mass growth and safe induction; compactness gives closedness and g(S)⊂S.

If S is infinite, some residue region contains a real angular interval at infinity in the following precise sense. Apply ordinary cylindrical semialgebraic cell decomposition with d as base coordinate. Above a sufficiently large d, each cell is a graph a=f(d) or a strip f_-(d)<a<f_+(d), with continuous semialgebraic bounds (infinite endpoints allowed). Each normalized endpoint direction f(d)/(f(d)+d), on nonnegative cells, has a limit by semialgebraic monotonicity. Graphs and strips whose two limiting endpoint directions agree contribute at most one slope; sequences of lattice points with bounded d and unbounded a contribute only 1. Thus some strip must have distinct endpoint directions. For any slope strictly between them in (0,1), the strip contains the tail of every fixed affine ray of that direction. In particular for a rational slope choose an integer ray direction with both coordinates multiples of M and a base in the residue class of the strip. This gives a ray in Q.

Choose such a rational direction whose leading g-iterate hits 1/2. These directions are dense: the two full branches of g have derivative magnitude at least 4/3, so the inverse images of their branch boundary form partitions of mesh at most (3/4)^k, and every finite preimage of 1/2 is rational. Apply ray propagation finitely many times, stopping at the first diagonal direction; all intermediate ratios are positive, finite, and unequal to 1. We obtain a complete arithmetic diagonal ray in Q. This contradicts the unconditional fatal-diagonal-ray theorem of [NoRegularInvariant.md](NoRegularInvariant.md), section 1: every such ray contains a one-return halter. Therefore S must be finite.

## 9. Finite limiting directions give uniform logarithmic tubes

For clarity, the finite set here is the limit directions of the entire candidate Q, not just of its root orbit. We show that every sufficiently large point of Q lies O(log s) transversally from one of finitely many interior irrational algebraic directions.

By compactness dist(x,S)→0 uniformly on Q as s→∞: otherwise a sequence violating it has a convergent subsequence defining an extra point of S. For sufficiently large mass, the nearest label in S is unique (trivial for a singleton). The exact normalized error and continuity of g force each successor label to equal g of the current label; mass always increases, so this remains true forever. Each label is eventually periodic. No label can lead to 1, because starting from a sufficiently large Q point of that label would give an actual infinite successful orbit with x→1, contradicted by section 2. Consequently no label equals 0 or 1/2 either. The rational-cycle argument in section 2 excludes every rational label (rationality is preserved by g).

Every periodic ratio r is algebraic independently of any defining polynomial: it is a fixed projective eigenline of an integral product of the two matrices in section 3, whose mass eigenvalue λ≤(3/2)^p and other eigenvalue |μ|≥2^p are distinct. The fixed-line equation is a nonzero quadratic or linear polynomial over Q. Every preperiodic ratio is algebraic as well, by rational fractional-linear inversion on its branch. Hence each label r is positive, finite, irrational algebraic.

For a cycle label, apply the backwards transverse series of section 3 along the future of ANY sufficiently large point with that label. All constants depend only on the finite set of labels and universal error bound, and future masses grow by at most (7/4) per step. This gives |a−r d|≤C log(s+2) uniformly on such points. For a preperiodic label, transport the bound back through its finitely many leading linear maps; each transverse multiplier is nonzero and each accumulated error O(log s). Thus the uniform bound holds on all sufficiently large Q points, including preperiodic ones.

## 10. Semialgebraic cells reduce these tubes to bounded offsets

Refine the fixed congruence modulus to be even, splitting each residue region if necessary. Intersect the regions with disjoint narrow cones around the finite interior labels (this preserves semialgebraicity and covers every sufficiently large lattice point of Q). Decompose each in cylindrical cells with d as base as in section 8. For d→infinity and a in the cone at ratio r, all masses are comparable to d.

We use two standard properties of one-variable real semialgebraic functions: eventual monotonicity (hence a limit in the extended reals), and the growth dichotomy. A function that is eventually nonzero has asymptotic form c d^γ(1+o(1)) with c nonzero and rational γ. These follow from the one-variable Puiseux theorem, e.g. Bochnak–Coste–Roy, *Real Algebraic Geometry*, and [Growth Dichotomy Lemma](https://doi.org/10.1016/j.jmaa.2013.08.044). They hold with arbitrary real coefficients, not just algebraic coefficients.

Discard cells with only boundedly many lattice points of their designated residue class. For a remaining graph a=f(d), the uniform logarithmic tube bound on its unbounded sequence of lattice points forces f(d)−rd to be bounded, since any unbounded semialgebraic function grows at a positive power rate. For a remaining strip with finite endpoints f_-, f_+ (intersecting the cone ensures this), first suppose its width is unbounded. The width is semialgebraic and then tends to infinity. For every sufficiently large integer d in the designated residue class, the strip contains integers a in its designated first residue within M of BOTH endpoints. Thus both endpoint deviations f_±(d)−rd are O(log d) along such d, forcing both bounded, contradiction to unbounded width. If the width is bounded, the unbounded sequence of designated lattice points forces both endpoint deviations bounded by the same growth dichotomy. In either case all large lattice points in every retained cell satisfy a uniform bound |a−rd|≤C. Finite cells and labels give a single constant.

Each bounded endpoint deviation tends to a finite real constant, and its difference from that limit is either eventually zero or O(d^(−ε)) for some ε>0 by growth dichotomy.

## 11. Positive-width irrational strips are impossible

Suppose some retained strip at irrational label r has distinct limiting endpoint deviations. It then contains a fixed nonempty open offset interval c₁<a−rd<c₂ for all sufficiently large d, within its fixed residue class (a mod M,d mod M). If r>1, the smaller coordinate is d; if r<1 it is a. In the first case the irrational rotation rd mod M along d in its designated residue progression is equidistributed, so a positive natural density of d admit an a in the designated residue class within the interval. In the second case solve for d, obtaining an interval of positive fixed length around a/r; use equidistribution of the irrational rotation a/r mod M instead. This uses Weyl equidistribution for an irrational arithmetic progression; shrinking the interval if necessary ensures an admitted lattice coordinate is unique. Therefore a positive natural density of smaller coordinates, and hence of the flat b=min(a,d)+constant in the fixed branch, occur in Q. The first budget A is linear in b asymptotically, so large b have all positive-budget reductions.

For b in [3^n,2·3^n), put k=n−1. All first k unconstrained reductions exist: the update b'=b/3+(2r_digit−3)/3 lies between b/3−1 and b/3+1/3. Hence after j steps the count lies between b/3^j−3/2 and b/3^j+1/2. At step k it is bounded by 7, leaving O(1) further steps. The first k residue digits depend only on b mod 3^k and form a bijection with the 3^k possible words. This follows inductively from the inverse affine maps L_r: each word determines exactly one residue, and the initial residue plus the next quotient determines the next digit uniquely. Thus over the entire interval each word occurs exactly three times.

The count N₀ of zero digits in the prefix, under uniform choice of b in this interval, has the binomial distribution with k trials and success probability 1/3. Chebyshev's inequality gives fraction O(1/k) with N₀>5k/12. Since the fixed strip admits a positive natural density of b, it admits some such typical b in every sufficiently large interval, with N₀≤5k/12. For these b, J(b)=2N₀(full)−L≤−k/6+O(1)→−infinity, and E(b)≥0. If the next label ratio is r'>0 and t is its fixed nonzero transverse multiplier as in section 5, then

    w'=t w+α+J(b)−r'(β+E(b)) → −infinity.

But the input w is bounded, the successor is in Q with mass tending to infinity, and section 10 bounds its offset uniformly. Contradiction. Thus no retained strip can have positive limiting width.

## 12. Thin irrational strips are impossible too

All remaining cells are graphs or strips whose endpoint deviations tend to the same finite constant. By section 10, every sufficiently large Q point has transverse coordinate

    w=a−rd=c+O(s^(−ε))

for some member c of a fixed finite set of real constants for its label, with one ε>0 uniformly over the finite cells. Unlike in section 5, these constants need not be algebraic.

For each transition between such cells, section 5's identity now gives

    e₁−r'e₂ = c'−t c + O(s^(−ε)).

There are only finitely many possible tuples (label r, c, c'). Let their number be K. In the compact interior sectors of Q, section 1 in fact gives two-sided bounds

    c₀ log s ≤ max(|e₁|,|e₂|) ≤ C₀ log s

for positive constants c₀,C₀ and all sufficiently large Q points. Indeed b is comparable to s, the lower length bound gives L≥log₃(2b+3)−1, and L≤|e₁|+|α|+e₂. The upper bound is uniform as before.

Follow any infinite successful orbit in Q. Its mass is unbounded and eventually grows by at most 7/4 per step. Choose a fixed R>2C₀/c₀+2. For arbitrary large U select K+1 indices at which log s first crosses the thresholds R^j U, j=0,...,K (take U above the initial mass logarithm). Since the one-step log overshoot is at most log(7/4), their error norms lie in pairwise disjoint intervals for large U. Their integer error vectors are distinct, all O(U) with constants depending only on fixed R,K. By pigeonhole two selected transitions have the same tuple (r,c,c') and thus the same r',t. Subtract their transverse identities to cancel the possibly transcendental constants:

    |Δe₁−r' Δe₂| = O(exp(−εU)).

The integer pair (Δe₁,Δe₂) is nonzero and O(U). Because r' is irrational algebraic, Δe₁−r' Δe₂ is nonzero; clearing denominators in Q(r') and taking the algebraic norm as in section 5 gives a lower bound c U^(−([Q(r'):Q]−1)). This contradicts the exponential upper bound for large U. No finite-direction Q exists, completing Theorem B.

## Scope and proof status

Sections 1–12 constitute a paper proof using the exact flat-drain identities, strict mass growth, and the earlier fatal-diagonal theorem. The arithmetic correction growth, exact J/E recurrences and their connection to positive-budget traces have been locally kernel checked in [DrainCorrectionGrowth.lean](DrainCorrectionGrowth.lean); the full semialgebraic theorem is not kernel-formalized. Standard external ingredients are cylindrical cell decomposition, one-variable semialgebraic growth dichotomy, irrational rotation equidistribution, and the algebraic norm bound. No finite trace or statistical assumption about the authentic root is used. There is still no claim that the actual blank orbit is infinite, or that any nonsemialgebraic proof system fails. In particular this closes the candidate class of polynomial inequalities with arbitrary fixed congruences, not the evolving ternary/history invariant class necessary to decide the root. The constructive exact inverse algorithm in [LogarithmicInverse.md](LogarithmicInverse.md) can be used to work on those remaining root-sensitive conditions.
