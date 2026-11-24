# Machine #623 admits no semilinear inductive safety invariant

**Agent 49, 2026-11-24.** The arithmetic core (fatal progressions, diagonal halters, and cofinality) is checked locally in Lean 4.36.0-rc2 against the exact source equations; the independent-rectangle and cofinality theorems passed [original-source CI 45347928813](https://github.com/FlareZ123/bb6/actions/runs/45347928813); the stronger diagonal theorem is awaiting its separate source-import run. The semilinear impossibility theorem below is a mathematical proof using that core. It does not resolve whether the blank trajectory halts.

**Complementary obstruction:** [AlgebraicCurveObstruction.md](AlgebraicCurveObstruction.md) proves that no infinite successful trajectory is eventually contained in a polynomial zero locus with algebraic coefficients. It uses transverse instability and the integer flat-drain corrections; the new proof is mathematical, not yet kernel checked. Polynomial inequalities remain outside that result.

## Main theorem

Let T be the certified high-level transition of #623, on D(a,d), whose blank-origin section is D(0,7). There is no semilinear set Q of pairs of nonnegative integers with all three properties:

1. (0,7) belongs to Q.
2. T succeeds at every point of Q.
3. Every successful successor of a point of Q belongs to Q.

In particular no Presburger-definable (first-order addition/order/congruence) predicate can be a complete safety invariant. By the standard Parikh and closure theorems for context-free languages, this also rules out ordinary context-free and regular inductive safety languages on the canonical finite raw tapes. This result is unconditional about the proof class, regardless of the actual blank-origin fate.

## 1. Fatal drain progressions and diagonal rays

Let F(A,b) mean drainB(A,b,z)=none for every z. The five exact identities from [FlatDrainSource.lean](FlatDrainSource.lean) imply the backward rules:

* F(0,3q+1).
* F(A+1,b) implies F(A,3(b+1)).
* F(A,b) implies F(A+1,3b+1).
* F(A,b), b>0 implies F(A+1,3(b-1)+2).
* F(0,b) implies F(0,3b+2).

They lift entire fatal rays b+3^e t to rays with period 3^(e+1). The base ray for first counter A is (3^(A+1)-1)/2 + 3^(A+1)t.

**Fatal-prefix theorem.** For every A,v,r>=0, there exist n,e with v+1<=e<=A+2v+1 such that every b=r+3^v*n+3^e*t, t>=0, is fatal at A.

Induct on v. At v=0 shift the base ray above r. At v+1, write r+2*3^(v+1)=3q+s with s in {0,1,2} and q>0. For s=0, recurse at (A+1,q-1). For A>0 and s=1,2, recurse at (A-1,q) or (A-1,q+1) respectively. At A=0 and s=1 the entire residue class is already fatal, and at A=0 and s=2 recurse at (0,q). Lifting back adds one to the exponent; the child first counter is at most A+1, giving the stated bound. Unlike the initial [FatalCylinder.lean](FatalCylinder.lean) result, there is no requirement A>=v; the zero-counter rule is essential. See [FatalAllPrefix.lean](FatalAllPrefix.lean).

**Arbitrary-period theorem.** Let p=3^v*m>0 with 3 not dividing m. Every progression r+p*j, j>=0, has a fatal member, for every A. The preceding ray intersects it by CRT. Explicitly choose u,w with 3^(e-v)*u=1+m*w and set t=u*(m*(n+1)-n). Then

    r+3^v*n+3^e*t = r+p*(n+1+w*(m*(n+1)-n)).

**Diagonal theorem.** For every P>0 and every a0,d0>=0,

    exists j>=0: T(D(a0+P*j,d0+P*j))=none.

Proof: after shifting both coordinates by P and taking steps of size 2P, a is positive and both parities and every fixed gap comparison are unchanged. In each nontrivial branch of T, the drain first counter A is constant along the ray, its second counter b increases by 2P, and its third parameter z is constant. The final even-right branch is exactly drainB(d+1-a,a+1,0) by unfolding the first drain step; the direct halt branch is immediate. The arbitrary-period theorem supplies a fatal input. The formal theorem is [FatalDiagonalSource.lean](FatalDiagonalSource.lean).

The earlier independent-rectangle result follows by taking P twice the given period: every rectangle D(a0+2P*i,d0+2P*j) contains a halter even with i=j. Shifting the base first proves that these diagonal halters are arbitrarily large on every such ray. These synthetic configurations are not asserted to be reachable.

## 2. Cofinality

Successful evalA(A,k,m)=(A',b',m') obeys A+b'<=A'+k+1 and m' >= m, by induction on A. Therefore successful drainB(A,b,d)=D(A',d') obeys A<=A'+b and d+2b<=d', by induction on b.

From these bounds and the explicit cases of highLevelNext:

    a+d >= 4K+10 and min(a,d)<=K and T(D(a,d))=D(a',d')
       imply min(a',d')>min(a,d).

For instance the odd far-left case has a'>=a-2d-8 and d'>=2d+11; the even far-left case has a'>=a-2d-4 and d'>=2d+6. In the odd far-right case a'>=d+5-2a and d'>=2a+1. In the remaining even far-right case, combine the evalA and drain bounds to obtain a'>=d-2a and d'>=2a+5. The a=0 cases increase the minimum from zero when the total is large; the a=d+2 case contradicts the premises; a direct halt contradicts success. The two far-left cases have d=min(a,d); the far-right cases have a=min(a,d) under the stated large-mass/small-minimum premise. All cases are formally checked, without a parity assumption.

The already certified mass theorem in [Parity623Source.lean](Parity623Source.lean) gives a+d>=7(n+1) at the nth surviving blank-root return. Thus any infinite orbit has simultaneous unbounded counters: if their minimum were bounded by K, then after the mass passes 4K+10 the minimum would increase on every step, a contradiction.


## 3. Uniform asymptotic dynamics

Write s=a+d and H(a,d)=(|a-d|,3 min(a,d)). Every successful transition of T satisfies

    T(D(a,d)) = D(|a-d|+O(log(s+2)), 3 min(a,d)+O(log(s+2))),

with signed errors bounded uniformly over all successful states (no root-history or survival-budget assumption).

To see this directly, the exact flat drain identities give a decreasing nonnegative counter b: each step with b>=2 replaces it by at most (b+1)/3<=b/2, and b=1 goes to 0 if successful. There are at most 1+floor(log2 b) steps for b>0. At each step the first counter changes by at most 1. If b changes to b', and z changes to z', the excess z'+3b'-(z+3b) in the four successful residue/zero-budget cases is respectively 0,4,2,1. Hence the final first counter differs from its input A by at most the number of steps, and final d differs from z+3b by at most four times that number. These estimates also follow from the previously certified [DrainLinearLogSource.lean](DrainLinearLogSource.lean) and Agent 8's digit-charge identity.

All positive-a nontrivial T branches are B(A,b,z), where A=|a-d|+O(1), b=min(a,d)+O(1), z<=5. This includes the equality branch a=d+2 (A=0,b=a) and the bundled final even-right branch. When a=0 the odd-d branch is B(d+1,2,2), and the even-d branch outputs (d,7). Direct halt is excluded by the success hypothesis. This proves the uniform error.

For positive mass set x=a/s, and define the continuous normalized leading map on [0,1]:

    g(x) = (1-2x)/(1+x) if x<=1/2,
           (2x-1)/(2-x) if x>=1/2.

Since H has mass s+min(a,d), normalization of the actual successor differs from g(x) by O(log(s+2)/s), tending to zero as s increases. Each branch maps onto [0,1] and has derivative of absolute value at least 4/3.

## 4. Semilinear impossibility proof

Suppose Q is a semilinear safe inductive invariant containing the root. Write it as a finite union of linear sets, each of the form

    base + n1*v1 + ... + nk*vk, with ni>=0 and vi in N^2.

Discard zero generators. In every nontrivial component, the signed gaps vi.a-vi.d must all be nonzero and have the same sign. Indeed, a zero gap is itself a nonzero diagonal generator. Opposite signs also give a positive integer combination with zero gap, whose direction is (P,P) with P>0. Either case puts a whole arithmetic diagonal ray into Q, contradicting section 1.

Let S be the limit slopes x=a/(a+d) of sequences of points in Q with mass tending to infinity. For each nontrivial linear component the contribution to S is the closed interval between the smallest and largest slopes of its nonzero generators. This follows by writing the slope of the sum as a mass-weighted average of generator slopes (the base becomes negligible). Conversely every intermediate weighted average is obtained in the limit by choosing two endpoint generator multiplicities in the appropriate ratio. Finite union commutes with this sequential limit construction by passing to a subsequence within one component.

Thus S is a finite union of closed intervals with rational endpoints, and 1/2 is not in S, by the common-sign gap condition. It is nonempty because induction from the root forces an infinite successful trajectory with unbounded mass.

Moreover g(S) is a subset of S: for any sequence defining a limit x, take its successful T successors, which are still in Q, still have mass tending to infinity, and whose slopes tend to g(x) by section 3.

If S contains a nondegenerate interval I, then every image g^n(I) is an interval in S and hence avoids 1/2. It stays in a single branch at each iteration, so its length grows by a factor of at least 4/3 at each step. This contradicts containment in [0,1]. Therefore S is finite and consists entirely of rational points.

**Rational-cycle lemma.** No rational periodic orbit of g lies in (0,1) while avoiding 1/2. Represent a rational slope by its unique primitive positive integer pair (a,d) with gcd(a,d)=1. Off the diagonal, H(a,d) has gcd

    gcd(|a-d|,3 min(a,d)) = gcd(|a-d|,3) in {1,3}.

Whenever the gcd is 3, division to the primitive pair decreases its mass: (max(a,d)+2min(a,d))/3 <= (a+d)/2. Thus these steps cannot continue forever. Once the gcd is 1, the new first coordinate is nonzero mod 3, the second coordinate is zero mod 3, and this pattern is preserved by H. The output remains primitive, positive, off-diagonal, and its mass strictly grows at every subsequent step. It cannot cycle. This proves the lemma.

Since g(S) is contained in finite S, any point in S is eventually periodic. An interior point cannot reach either endpoint without hitting 1/2: g(x)=0 precisely at 1/2, and g(x)=1 precisely at 0 or 1. It cannot have an interior cycle by the rational-cycle lemma. Consequently S is contained in {0,1}.

All nonzero generators in each linear component therefore point along a single axis. Each component has one coordinate fixed at its base value, including the case of a singleton. The finite union Q has a uniform bound on min(a,d). Its infinite successful blank trajectory contradicts the cofinality theorem of section 2. This completes the proof.

## 5. Consequences for language certificates

The classical equivalence between semilinear sets and Presburger-definable subsets of N^k gives the arithmetic corollary. A raw-tape language invariant restricted to the D-section must also be a safe inductive invariant for T, by the certified acceleration. The finite canonical encoding of D(a,d) has fixed control/head and boundary markers and the variable blocks (10)^(a+1) 0 1^d. If the invariant language is context-free, remove the fixed prefix/suffix by quotients, take the inverse of the homomorphism mapping X to 10, a separator to 0, and Y to 1, and intersect with the regular language X* separator Y*. The Parikh image, projected to the X and Y counts, is semilinear and gives exactly Q. Context-free languages are closed under these operations, and Parikh's theorem makes their count images semilinear. Contradiction.

In particular ordinary regular languages and standard FAR certificates cannot prove this machine nonhalting, irrespective of their state count. The same conclusion holds for arithmetic abstractions whose concrete accepted set is semilinear, including finite unions of rational polyhedral regions with congruence conditions. Nonlinear and nonsemilinear invariants, history-sensitive proofs, and regular languages on enriched encodings with nonsemilinear interpretation are not excluded.

## Proof status and next direction

The generic prefix and period theorems, diagonal theorem, cofinality inequalities, and earlier independently-periodic root contradiction are locally kernel-checked with the standard Lean axioms only, without sorry or native decision. The source-importing versions are wired into the manual flat-drain workflow against unmodified Cryptids c86f15861709b76042998c5211c7b2f83991621b. The normalized-dynamics, limit-slope and semilinear proof is presently a paper proof, not a fully formalized theorem. No claim is made that the actual blank orbit is infinite.

The remaining objective is a root-sensitive argument using genuinely nonsemilinear data, e.g. an evolving ternary digit-scale relation, not another finite-modulus or polyhedral invariant search.
