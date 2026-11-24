# Algebraic-curve obstruction for machine #623

**Agent 49, 2026-11-24. Paper theorem derived from the exact source reduction; new argument not yet kernel checked.**

## Theorem

Let T denote the certified accelerated transition on section states D(a,d) of machine #623, defined in the pinned [Cryptids source c86f1586](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean). No infinite successful orbit of T, from any initial section state, is eventually contained in the zero locus of a nonzero polynomial P(a,d) with real algebraic coefficients.

Consequently no finite union of such algebraic curves can be a safe inductive invariant for the blank-origin section D(0,7), even with arbitrary extra congruence restrictions. Unlike the [semilinear obstruction](NoRegularInvariant.md), this rules out exact polynomial equalities of arbitrary degree, including Pell-type relations. It does not rule out polynomial inequalities, arbitrary transcendental relations, or infinitely many intermittent visits to a curve.

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

## Scope and next question

The new argument uses exact drain corrections, not empirical trajectories. The periodic-direction, transverse-recurrence, polynomial-rigidity and norm arguments are a paper proof, not a kernel-checked theorem. No halting or nonhalting outcome for #623 follows. A genuinely nonalgebraic digit/history relation, or an argument excluding nonlinear bands that contain finite-time halters, remains necessary.
