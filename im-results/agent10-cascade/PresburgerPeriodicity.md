# Presburger safety invariants and periodic reset itineraries

**Status (2026-11-24): paper theorem over the exact source ResetParent grammar, with a locally kernel-checked recurrence/congruence lemma.** The complete cylinder density theorem used below is a paper proof, not a source-integrated Lean result. This does not decide #746 or BB(6). It converts a broad invariant-synthesis problem into a concrete periodic-itinerary problem and gives a finite exact certificate test for any proposed period.

The complementary [two-coordinate finite exclusion](PeriodicBetaSearch.md) now rules out every periodic itinerary of total level increment D<=80 by exact computation and paper completeness proof. It does not resolve the unbounded-period case of the equivalence below.

## 1. Equivalence theorem

For a nonfatal height h and its unique sweep level k, set p=2^k and x=(h+k+4)/p. Validity means 4p<h+k+4 and h+k+5<8p. An inductive safety set is a set of valid heights closed under every genuine ResetParent edge, hence excluding all fatal gate heights. Consider predicates P(h,k,p) definable in ordinary Presburger arithmetic, with p interpreted as 2^k (the exponentiation is external to the formula). Quantification over auxiliary integer variables is permitted. Bounded-level exceptions are permitted.

**Theorem.** The authentic blank root admits a Presburger-definable inductive safety set of this kind if and only if its reset orbit is infinite and its sequence of tokens (a,delta) is ultimately periodic, where a is the reset valuation and delta=k'-k is the level increment. The same equivalence applies to any valid prepared root from which every nonfatal reset follows the same exact grammar.

This is strictly stronger than excluding finite Boolean combinations of fixed residue classes and normalized-height intervals: it also handles arbitrary affine linear inequalities in h,k,2^k, including very thin affine strips whose width in x tends to zero.

### 1.1 Density forces thin rational strips

By ordinary Presburger quantifier elimination, P is a finite Boolean combination of affine integer inequalities and fixed-modulus linear congruences. Substitute h=xp-k-4 in an inequality Ah+Bk+Cp<=E:

    (Ax+C)p + (B-A)k - 4A-E <= 0.

If A=0, its truth is eventually constant in k. Otherwise its sign, except within distance O((k+1)/p) of the rational threshold -C/A, is exactly the sign of Ax+C. For every fixed modulus, p=2^k modulo that modulus is eventually periodic in k (the 2-primary part is eventually zero, and the odd part is a unit). All the congruences therefore depend, beyond a fixed level, only on h mod m and k mod M for suitable common moduli.

Let T be the finite set consisting of 4,8 and all rational thresholds in [4,8]. Choose a common constant C0>0 and sufficiently large K so that outside the strips

    |x-t| <= C0*(k+1)/2^k,  t in T,

the formula agrees with a constant truth value on each open threshold interval and residue pair. More precisely, if a point outside all the strips is accepted, then every sufficiently large valid point of the same residue pair whose x lies in any fixed compact subinterval of that threshold interval is accepted. This follows by stabilizing the finitely many inequality signs.

But [ModularCylinderDensity.md](ModularCylinderDensity.md) supplies arbitrarily large prepared points in that residue pair and open interval with a genuine finite reset chain to an authentic-sector fatal height. An inductive safety set cannot contain any such point. Thus every sufficiently large point of any safe P lies in those finitely many thin rational strips.

### 1.2 Thin strips force exact transitions between rational slopes

Suppose an infinite reset orbit is confined to these strips. Heights strictly increase, so the nondecreasing sweep levels tend to infinity (each bounded level band is finite). Write x_i=t_i+O((k_i+1)/2^k_i), t_i in T. For sufficiently large levels the strips of distinct thresholds are disjoint.

The exact source recurrence from [PeriodicRigidity.md](PeriodicRigidity.md) is

    X'=3^a*(X+16p+2k+5)/2^(a+1),  X=2h+5.

With c=3^a/2^(a+1+delta), the normalized recurrence becomes

    x'=c*(x+8)+c/2^k+(k'+3/2)/2^k'.

The source integer h+k+5+8p lies strictly between 12p+1 and 16p, so its 2-adic valuation a<=k+3. Since the next valid centered height exceeds 4*2^k' for k'>=1, and X'<16p*(3/2)^a, we have delta<2+a*log2(3/2). In particular a,delta,k' are O(k). Also c<2/3 since x'>c*(x+8) and x'<8.

It follows, uniformly over the finitely many t,t' in T, that

    | c*(t+8)/t' - 1 | = O((k+1)/2^k).

Use Matveev's lower bound for a nonzero product of powers of fixed positive rationals minus 1: for fixed positive rationals r1,...,rs and integers b_i with max |b_i|<=B, the absolute value, if nonzero, is at least c1*B^(-c2), for positive constants depending only on the rationals. Apply this with rationals 3,2,(t+8)/t' and exponents a,-(a+1+delta),1. Factors equal to 1 may simply be removed. Since B=O(k), the polynomial lower bound eventually exceeds the exponentially small upper bound. The finite set of pairs allows one common sufficiently large cutoff. Hence every sufficiently late transition satisfies the **exact** slope equation

    t' = 3^a*(t+8)/2^(a+1+delta).                      (A)

The use of Matveev here is essential to this proof: merely observing that the error tends to zero would not justify equality when a,delta can grow.

### 1.3 The finite rational slope path is deterministic

Let v2 denote the 2-adic valuation of a nonzero rational. If v2(t)<3, then v2(t+8)=v2(t) and (A) decreases the valuation by at least one. Once this happens, the valuations decrease forever, contradicting the finite slope set. If v2(t)>3, the next valuation is at most 2. Consequently every sufficiently late slope has v2(t)=3.

Write t=8n/q with n,q positive odd, gcd(n,q)=1, q/2<n<=q. The odd denominator q can only decrease by divisibility under (A), with any decrease caused by cancellation of a power of 3. It therefore eventually stabilizes. If 3 divides the stabilized q, every subsequent a must be zero. With a=0 and slopes in [4,8], delta=0 is forced, except potentially t=8,delta=1,t'=4; the latter is impossible because v2(t')=2. This would keep the level bounded. Therefore gcd(q,6)=1. If q=1, t=8 at every late phase and (A) forces 3^a=2^(a+delta), hence a=delta=0, another contradiction. So q>1 and all late slopes satisfy q/2<n<q.

For stabilized q let w=v2(n+q), m=(n+q)/2^w. Then (A) becomes

    n'=3^a*m,    a+1+delta=w,    q/2<n'<q.

The equation for w follows from oddness of n'. There is at most one a in [0,w-1] meeting the interval condition, because consecutive candidate numerators differ by a factor of 3 and the interval has ratio 2. Thus each slope uniquely determines the next slope AND both token parameters. An infinite deterministic path in the finite slope set is ultimately periodic. Its eventual period has positive total level increment D, since levels are unbounded.

### 1.4 Converse: an ultimately periodic valid orbit gives a Presburger invariant

Take the finite prefix of such an orbit and a nonempty repeated word of positive total level increment D. The exact all-word rigidity theorem in [PeriodicRigidity.md](PeriodicRigidity.md) shows that each phase i has a fixed rational triple (alpha_i,beta_i,gamma_i) such that

    2h+5 = alpha_i*2^k + beta_i*k + gamma_i

at every occurrence of the phase. The corresponding levels are exactly k_i+jD for integers j>=0. Clearing denominators gives a linear equality in h,k,p; the level set is expressed by a lower bound and one fixed congruence. A finite union of these phase predicates and the finitely many initial points is Presburger-definable, and, on valid points with p=2^k, equals the actual orbit. Determinism and infinitude give closure and safety. This proves the equivalence.

## 2. A complete finite checker for any proposed infinite period

The existing rigidity theorem gives the unique candidate phase-0 coefficients for a word whose exact affine composition is

    P X'=R X+S*2^k+C*k+E,   k'=k+D.

Specifically, G=2^D and

    alpha=S/(PG-R),
    beta=C/(P-R),
    gamma=(E-P*beta*D)/(P-R).

Both denominators PG-R and P-R are odd and nonzero (P even, R odd). Applying each token successively transports the coefficients:

    r=3^a/2^(a+1)
    alpha'=r*(alpha+16)/2^delta
    beta'=r*(beta+2)
    gamma'=r*(gamma+5)-beta'*delta.

The triple returns to itself after the word, and the levels at every phase are k_i+jD. Cyclic rotation of the word gives the same unique phase triple, so all phase denominators are odd.

### 2.1 Three samples certify every period boundary

Clear the phase-0 denominators by a positive odd Q. The numerator at the jth period boundary has the form

    N_j = A*G^j+B*j+C.

The characteristic polynomial (T-G)(T-1)^2 gives

    N_(j+3)=(G+2)N_(j+2)-(2G+1)N_(j+1)+G*N_j.

The coefficients sum to 1. If N_0,N_1,N_2 are all congruent to Q modulo 2Q, then induction gives that congruence at every boundary, exactly certifying odd integrality of X_j=N_j/Q. This all-j congruence theorem, the recurrence and the second-difference identity are locally kernel checked in [PeriodicCertificate.lean](PeriodicCertificate.lean) (Lean 4.36.0-rc2; standard axioms only).

Inside a block, forward substitution from an integral boundary shows each rational X has denominator dividing a power of 2. Backward substitution from the next integral boundary shows its denominator divides a power of 3. Hence every intermediate X is integral. The backwards single-token equation subtracts the odd integer 16p+2k+5 from an even integer (the integral quotient of 2^(a+1)*X' by the odd 3^a), so all intermediate X are odd as well.

### 2.2 Exact all-j band inequalities

For any phase triple the lower and upper strict validity gaps, expressed in X, are

    (alpha-8)*2^k+(beta+2)*k+gamma+3,
    (16-alpha)*2^k-(beta+2)*k-gamma-5.

The gap has the form f(k)=A*2^k+B*k+C with rational coefficients. On k=k_i+jD, D>0:

* If A<0, eventual negativity rejects the word.
* If A=0, nonnegativity of B and positivity at the starting level are necessary and sufficient for strict positivity at all levels.
* If A>0, the discrete first difference A*(G-1)*2^k+B*D strictly increases. The minimum occurs at the first j>=0 with nonnegative next difference. Find that j by doubling then binary search, and test the minimum exactly.

The same method checks X>=5 by testing X-4>0. Together with phase-0 equality to 2h+5 and the three odd-integrality tests, these conditions are necessary and sufficient for an exact infinite ResetParent chain from a given prepared (h,k). Sufficiency follows directly from the unified exact grammar; no additional simulation is required.

### 2.3 Exact existence test for any arbitrarily late prepared start

An affine-exponential gap is eventually strictly positive iff its coefficient triple is lexicographically positive. First test this for both band gaps at every phase. It also implies eventual natural height because the lower band grows exponentially.

Write the phase-0 value as (A*2^k+B*k+C)/Q, Q odd. Its first three odd-integrality conditions are equivalent to

    A*2^k+B*k+C = Q (mod 2Q),
    A*(G-1)*2^k+B*D = 0 (mod 2Q),
    A*(G-1)^2 = 0 (mod Q),   for k>=1.

These come from the first and second differences; the last uses invertibility of 2^k modulo Q and the automatic factor 2. The power residue 2^k mod 2Q has period L=ord_Q(2) on k>=1 (take L=1 when Q=1). For each residue s mod L, substitute its power residue into the first two conditions, solve the first as a single linear congruence in k and intersect it with k=s mod L by the generalized CRT. Every compatible class is unbounded. The gap conditions then hold for all sufficiently large starts in that class. Conversely any infinite prepared period has some start k>=1, so the finite test is complete.

The exact rational Python implementation [periodic_certificate.py](periodic_certificate.py) provides certify(word,h,k) and possible_prepared_period(word). It checks 2,770 small regression words by independently substituting their phase equations; no feasible period was found in that finite sample. The algorithm can be expensive in the multiplicative order of Q, but it is a complete test for each fixed word, not a search cutoff.

## 3. No period with exactly one positive valuation, of any length

This is an unconditional all-parameter exclusion of a period family, not a finite scan.

Use the stabilized rational slope graph t=8n/q above. The existing second-difference theorem gives q divides (2^D-1)^2. Suppose the repeated word consists of a single positive token (a,delta) followed by m zero-valuation tokens, L=m+1. Every zero token has delta=0, and D=delta>0. Immediately before the positive token put e=(q-n)/2. It is a positive integer, gcd(e,q)=1. The positive token sends the numerator to 3^a*(q-e)/2^(a+delta). The subsequent m zero tokens halve the gap q-n on every step. Returning to n=q-2e gives

    q*(2^(a+delta)-3^a)=e*(2^(a+delta+L)-3^a).

Set U=2^(a+delta)-3^a, V=2^(a+delta+L)-3^a. We have V>0: the slope fixed point for this positive affine word has positive numerator and positive denominator V. Thus U>0. Since gcd(q,e)=1, q=V/gcd(U,V). The gcd divides 2^L-1, because V-2^L*U=3^a*(2^L-1) and gcd(U,3)=1. Therefore

    q >= V/(2^L-1)
      = 2^(a+delta)+U/(2^L-1)
      > 2^(a+delta).

On the other hand a positive normalized slope transition has n'/q>1/2 and n/q<1, giving 2^delta<2*(3/2)^a. Since a>=1, delta<=a. Therefore q>2^(2delta)>(2^delta-1)^2, contradicting the necessary divisibility. Every genuine periodic itinerary must contain at least two positive tokens.

Caution: the stronger naive inequality q>(2^D-1)^2 is false for general rational slope cycles. For example q=161, numerators 153,157,159,135,111 form a cycle with tokens (0,0),(0,0),(3,2),(1,1),(2,1), D=4. Here q<225, although q does not divide 225. Also q=865 has a cycle with two positive tokens and D=5, q<961. Thus the one-positive-token proof cannot simply be extrapolated by size.

## 4. Consequences and limits

The Presburger equivalence makes a proposed finite affine/residue safety proof meaningful only if it can produce an actual periodic suffix. The finite certificate above closes the all-time validity and integrality obligations for any proposed word. The authentic root must still be shown to reach the certified prepared point; no such word or root suffix is presently known. The theorem does not constrain arbitrary physical-tape regular/FAR invariants, and cannot by itself prove nonhalting or aperiodicity of the blank orbit.

External classical results used: ordinary Presburger quantifier elimination with fixed divisibility predicates (e.g. [Hamkins' quantifier-elimination exposition](https://jdh.hamkins.org/quantifer-elimination/)); Matveev's theorem on products of powers of positive algebraic numbers, in its rational fixed-base specialization (e.g. [Theorem 1, DOI 10.1007/s11139-025-01306-0](https://doi.org/10.1007/s11139-025-01306-0)). These are paper-level dependencies, not Lean axioms added to the project.
