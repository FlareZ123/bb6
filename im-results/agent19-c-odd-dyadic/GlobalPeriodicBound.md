# Global finiteness of candidate periods for the normalized root32 shadow

This theorem concerns the **ordinary rational-shadow grammar** of [ShadowPeriodicity.md](ShadowPeriodicity.md), with denominator C=211, U,V>422 and S=U+2V=5 mod 211. It rules out unbounded primitive periods of eventually periodic cost words. It does not establish that no candidate period exists, that every infinite cost word is eventually periodic, or that the authentic Machine C root is nonhalting. The proof below is a mathematical paper argument, not a Lean theorem.

## 1. Finite index and a rational product gap

For any putative eventually periodic cost word use its primitive period, with binary repetend numerator a/q in lowest terms, q odd, b=ord_q(2), ell its number of one digits, W=3b+ell, and delta=ell-b/2. The previously established necessary conditions in ShadowPeriodicity.md are:

* 211 divides q; W is even; k=211 W/q is a positive even integer.
* delta is nonzero; 0<ell<b, so |delta|<b/2.
* b is even (because ord_211(2)=210).

In particular q/b<422. Let s be the number of distinct primes dividing q, I=phi(q)/b, and K=kI. Since b is the lcm of the prime-power orders, each of which divides its even local totient, v2(I)>=s-1. More explicitly, if the local totients have valuations e_i>=1, then v2(b)<=max e_i, so v2(I)>=sum e_i-max e_i>=s-1. Since k is even, 2^s divides K. Also b<=phi(q)/2^(s-1) implies 2^(s-1)<422 and s<=9.

Write the remaining distinct prime factors, other than 211, in increasing order p_1,...,p_r, r=s-1<=8. The totient identity gives

    A := K * product_i p_i/(p_i-1) = 210 W/b = 735 + 210 delta/b.

Thus K is a positive multiple of 2^(r+1), K<840, and A!=735. The exponent of each prime in q has dropped out of this equation.

**Proper-prefix obstruction.** For any j<r, A_j=K*product_{i<=j} p_i/(p_i-1) is not 735. If equality held and j>0, the largest p_j would divide 735*product_{i<=j}(p_i-1), but it divides none of the factors p_i-1. Hence p_j divides 735=3*5*7^2 and every p_i lies in {3,5,7}. The equality after clearing denominators then has 2-adic valuation >=r+1 on the left, and exactly j+1_{5 in prefix}<=j+1<=r on the right. Contradiction. For j=0 the conclusion follows because K is even.

This alone implies a positive gap uniform across every possible prime support. Suppose A tends to 735 along a sequence of candidates. Pass to a subsequence with fixed r,K (finite choices). For each sorted prime coordinate, pass to a subsequence on which it is constant or tends to infinity. The constant coordinates form a prefix because the primes are sorted. If any prime escapes, the limiting A is that proper-prefix product, which cannot be 735. If none escapes, A itself is constant, hence exactly 735, which contradicts delta!=0. Thus no candidate sequence can have A approach 735.

For an **explicit** bound, define

    P_0 = 2,
    P_(j+1) = 2 + 2*735*255*P_j^j      (0<=j<8),
    epsilon = 1/(2 P_8^8).

The sequence is increasing. For any first coordinate p_(j+1)>P_(j+1) with earlier coordinates p_i<=P_i, j<r, the nonzero proper-prefix gap is >=1/P_j^j, because the cleared denominator product is <=P_j^j (empty product 1). If A_j>735, positivity of all remaining factors gives A>A_j and the same gap. If A_j<735, put x=1/(p_(j+1)-1). The tail ratio is <=(1+x)^(r-j)<=1+255x by the binomial theorem and 0<x<=1. Hence A-A_j<=735*255/(p_(j+1)-1)<1/(2P_j^j). The full gap is at least 1/(2P_j^j)>=epsilon. If no coordinate escapes, the full product denominator is <=P_r^r and the nonzero gap is at least 1/P_r^r>=epsilon. This also covers r=0. Thus every candidate satisfies

    210 |delta|/b = |A-735| >= epsilon.

This intentionally coarse constant avoids any enumeration of supports or approximation of rational products.

## 2. Elementary character-sum discrepancy bound

For any odd q and a reduced residue a, its powers-of-two orbit is the coset aH of H=<2> in the finite group G=(Z/qZ)^*. Write b=|H| and I=|G/H|. The number ell of residues in aH above q/2 is the number of one digits in a binary period: long division multiplies the current reduced residue by 2 and emits the next bit according to which half it lies in.

By character orthogonality on G/H, extending all characters by zero on nonunits,

    ell = (1/I) sum_(chi trivial on H) conj(chi(a)) sum_(q/2 < x < q) chi(x).

The principal character contributes phi(q)/(2I)=b/2, by the unit involution x -> q-x. We give an elementary bound on each nonprincipal character sum, to make the constants and the effectiveness independent of an external asymptotic theorem.

Let chi* be primitive of conductor f|q inducing the nonprincipal chi (so f>1). For every interval J of consecutive integers, the primitive estimate is

    |sum_(n in J) chi*(n)| <= sqrt(f) (1+ln f).

Here is a finite Fourier proof. Full f-periods contribute zero. On a remaining interval of length <f, expand chi* via the finite Fourier transform. For t invertible modulo f, its Gauss sum has constant absolute value; for t noninvertible it is zero: a primitive character is nontrivial on the kernel of the reduction of units modulo the proper divisor f/gcd(t,f), and multiplication by a unit from that kernel preserves the additive exponential while multiplying the character by a nontrivial scalar. Parseval gives sum_t |G(t)|^2=f phi(f), so the common nonzero absolute value is sqrt(f). For 0<t<f, the finite geometric sum over J has absolute value <=1/|sin(pi t/f)|<=f/(2 min(t,f-t)). Fourier inversion and summation over t bound the character sum by sqrt(f) times the harmonic sum up to floor(f/2), hence by sqrt(f)(1+ln f). This argument also proves the estimate for arbitrary-length intervals by the zero full periods.

For chi modulo q induced by chi*, exclude the primes of q absent from f by inclusion-exclusion. Each divisor d of the product of those primes contributes chi*(d) times a primitive sum over the interval of n/d with n divisible by d. There are at most 2^s such terms, where s is the number of distinct prime factors of q. Consequently

    |sum_(q/2<x<q) chi(x)| <= 2^s sqrt(q)(1+ln q).

Averaging the nonprincipal terms of the orthogonality formula gives

    |delta| <= 2^s sqrt(q)(1+ln q).

For candidate q, s<=9 and b>q/422, so

    |delta|/b < 422*512*(1+ln q)/sqrt(q).

In particular the imbalance fraction tends to zero uniformly as q grows, regardless of its prime support. The uniform nonzero product gap proves that candidate denominators form a **finite set**.

## 3. Effective universal denominator bound

For q>=1, ln q <= 4(q^(1/4)-1), hence 1+ln q <=4q^(1/4). Combine the inequalities:

    epsilon <= 210 |delta|/b < 210*422*512*4 / q^(1/4).

Therefore every candidate satisfies

    q < Q := (2 P_8^8 * 210*422*512*4)^4,
    b <= phi(q) < q < Q.

The bound Q has 8,117,510 binary digits (the recurrence is easily evaluated with exact integer arithmetic). The proof does not assume a fixed prime support or cap the prime powers. Q is enormous; it is a theoretical finite search reduction rather than a practical enumeration cutoff. The sharper per-support lift bound in ShadowPrimeLifts.lean and PrimeSupportScan.py remains useful computationally.

**Main consequence.** Every infinite ordinary non-leaf path of the normalized root32 grammar whose costs are eventually periodic has one of a finite, effectively enumerable set of primitive cost periods. The threshold is for periods, not for a preperiod or for arbitrary inverse paths. In particular it does not combine with density-zero coverage to imply mortality: remaining costs may be aperiodic.

## 4. Finite decision procedure for existence of periodic tails (prepared shadows)

This consequence concerns existence over all integral shadows with the given residue, not reachability from an authentic root. For each q<Q and each reduced odd numerator a with 0<a<q, obtain its primitive binary repetend and the cyclic list of positive gaps d_i; odd numerator ensures the word B=a(2^b-1)/q has its bit at position 0 set. Ignore all-direct and words failing the necessary constraints. Set D=2^b, h=(D-1)/q, B=ah and k=CW/q. For each starting parity s, unroll the affine recurrence over a period as in ShadowPeriodicity.md to get K_s.

An infinite periodic tail necessarily has, at cycle starts,

    U=(a S+J)/q,  J=(C K_s-D a k)/h,

by the vanishing integer error argument. If J is not an integer, no integral S,U can satisfy this equation. Otherwise take S in each residue class modulo M=8qD, restricting S=5 mod C and S=s mod 2. Compute U and V=(S-U)/2, and unroll the exact affine recurrence over four consecutive cycles (without demanding positivity of the chosen small representative). Require every U_i,V_i to be integral, every U_i=S_i mod 2, and the actual direct/high congruence and non-leaf tests, interpreting high valuations as divisibility by 2^d even for nonpositive representatives. Check each cycle boundary U'=U+a k, S'=S+CW. Check that the orbit slope at each phase lies strictly between zero and one: it is the cyclic fraction a_i/q with 2^d a_(i+1)=a_i+q.

Why this finite test is exact: increasing S by M changes U at the start by 8Da and propagates through every phase by exactly 8D a_i, so U,V integrality, residues modulo 4, and high-edge divisibility tests are invariant (d<=b, so 2^d divides D). With S sufficiently large, positivity U_i,V_i>2C holds at every phase because both slopes are strictly positive. At each new cycle the phase values increase by a_i k and (q-a_i)k/2 respectively, both integers and positive. Both increments are even, since a_i,q odd and k even. Their residues modulo 4 repeat after at most two cycles; four are a safe finite test. High-edge divisibility for every cycle also follows from the recurrence and parity: 2^(d-1)*(U'-C(2+o))=U+V-Co, with U' congruent to S'=o mod 2, so the quotient is even. Direct edges preserve the prescribed congruences. All remaining cycles obey the same congruences, positivity and leaf tests. Conversely any existing positive periodic tail yields one such residue class, and decreasing S by a multiple of M preserves the tested congruences and boundary equations. Thus enumerating the bounded q, numerators, parities and finite residue classes decides whether **any** such periodic tail exists in the prepared ordinary grammar.

This is a decidability theorem with a very large effective search, not a computed answer to that decision problem. It says nothing about the possible existence of an aperiodic infinite path, and reachability of a prepared periodic tail from a particular root would still need a separate argument.
