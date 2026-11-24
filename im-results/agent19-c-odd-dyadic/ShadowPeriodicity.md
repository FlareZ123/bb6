# Periodicity obstruction for ordinary rational-shadow paths

**Status:** the constant odd-cost existence classification and explicit infinite non-leaf examples are kernel-checked in Lean 4.36.0-rc2 in [ShadowPeriodicFamilies.lean](ShadowPeriodicFamilies.lean). The general periodic-word number-theoretic obstruction below is a paper argument; the necessary-condition denominator census is computational. The sound original-source shadow checker itself is separately accepted in CI 45379626167. None of these claims decides the authentic root32 family.

## Ordinary edges

Let C be a positive odd integer. Consider positive integral shadow coordinates U,V, with U,V>2C. Write S=U+2V, o=(U+V) mod 2 and Q=U+V-Co. The direct edge (cost d=1) is available if V is even, and has U'=U+V+2C, V'=(V+2C)/2. An ordinary high edge of depth n has d=n+2, with d<=v2(Q), d mod2=(U+1+o) mod2, U'=Q/2^(d-1)+C(2+o), V'=(S+C(3d+1)-U')/2. We consider only integral edges. The forbidden leaf test can be added, but the necessary obstruction below holds even without that test.

Each edge preserves U,V>2C: direct is immediate; high has U'>2C and U'<= (U+V)/2+3C, so V'>=U/4+3V/4+2C. Both types obey

    S'=S+C(3d+1),
    2^d U'=U+S+C[2^d(2+o)-2o],
    o=(S+1+d) mod2.

In particular, a direct-only infinite tail would repeatedly halve V-2C, a strictly positive integer, which is impossible.

The three exact root32 residual shadows of Root32ShadowRoot.lean have both numerators divisible by 105. Dividing by 105 replaces C=22155 by C=211. All ordinary transitions preserve this common factor (105 odd), as well as their parity, v2 conditions and forbidden-leaf status (105=1 mod4). The initial normalized S is 5 mod211 for every j and each of D,L,P, and its residue mod211 is preserved. The initial normalized U,V exceed 422.

## Exact classification of constant odd-cost paths

For every positive C and odd d>=3, a positive infinite ordinary path (U,V>2C) with constant cost d and no forbidden leaves exists **if and only if**

    2^d-1 | C(3d+1)/2.

Necessity is stronger than assuming a particular affine shape. Put D=2^d, q=D-1, W=C(3d+1). Along any infinite constant odd-cost path, V is even and U parity is fixed; hence B=C[D(2+o)-2o] is constant, S'=S+W and D U'=U+S+B. The integer error

    e=q^2 U-q(S+B)+D W

satisfies D e'=e. A nonzero integer error would have strictly decreasing positive absolute value forever, so e=0 everywhere. Subtracting consecutive zero errors gives q(U'-U)=W. The divisor q is odd, W is even, and thus q divides W/2.

Conversely let delta=C(3d+1)/(2q) be integral, A=D/2 and z_k=2C+delta*k. Set

    U_k=2z_k+2C,
    V_k=(D-2)z_k+D*delta-2C.

Then U_k,V_k>2C, both are even, U_k+V_k=D(z_k+delta), and the exact high-edge equations give the successor (U_(k+1),V_(k+1)). Since V is even, no point is a forbidden leaf.

In particular the prime denominator C=7 has an explicit infinite non-leaf constant-cost path of d=3,

    (16+10k,32+30k) -> (26+10k,62+30k).

A second exact example at C=15 alternates costs 1 and 3:

    (31+42k,34+84k) -> (95+126k,32+42k) -> (31+42(k+1),34+84(k+1)).

Both coordinates stay above 2C and both right coordinates are even. These examples refute denominator-independent mortality, including a claim restricted to all prime denominators. They are **not** paths at C=211 and do not establish reachability of any actual Machine C target. Any proof of root32 shadow mortality must use more than positivity, monotone mass, odd denominator, and avoidance of the existing forbidden leaf.

The exact theorem `BB6.Agent19PeriodicFamilies.constant_odd_iff`, its two directions, the integer-decay and affine-drift lemmas, and both explicit examples compile locally using only Lean core 4.36.0-rc2 (commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a). Axiom profiles are [propext, Classical.choice, Quot.sound] for the classification and drift, and [propext, Quot.sound] for the examples and integer decay; no sorryAx or native-decision axiom. The module defines the ordinary arithmetic edge relation parametrically; it does not import the source-specific root32 checker.

## No uniform fuel for the actual D root32 shadow family

The previous constant-cost examples use other denominators. The actual normalized C=211 D root family has a separate exact obstruction, proved in [Root32Unbounded.lean](Root32Unbounded.lean). From its initial coordinates

    U=309991342080*j+158931736572
    V=588402769920*j+301672535206

the ten successive costs 1,1,1,1,1,1,1,3,1,2 are legal and non-leaf for every natural j. The terminal coordinates are

    U'=603867580260*j+309601306391
    V'=441464650830*j+226337755466
    V'-422=6*(73577441805*j+37722959174).

Each subsequent direct edge halves V-422, increases U, and avoids the forbidden leaf as long as V-422 is even. The coefficient 73577441805 is odd. For every n, successive single-bit lifting therefore produces a natural j with 2^n dividing 73577441805*j+37722959174. This gives an ordinary non-leaf path of length at least n+10 from the D seed. The corresponding infinite 2-adic index is the rational number -37722959174/73577441805; this is not a nonnegative integer index.

The Lean module works at the unnormalized C=22155 and proves both `unboundedD` and `d_checker_no_uniform_fuel`. The latter uses the definitions of the existing recursive `excluded` checker, proving by induction that any non-leaf path longer than its fuel forces false at every precision. In particular for every fixed f some j has false D-checker result for **every** p. The seed affine forms are exactly the expansion of the D `rootShadow` formulas in Root32ShadowRoot.lean. Local Lean 4.36.0-rc2 accepted these theorems with ordinary axioms only against the verbatim relevant executable definitions of Root32ShadowArithmetic.lean. Full repository import/CI acceptance has not been performed (local GitHub checkout is blocked by DNS).

Consequences: a finite uniform depth or fixed finite family of successful residue cylinders cannot close the ordinary D search across all natural j using this leaf test. There is no contradiction with the density-zero theorem: the exceptional 2-adic index has measure zero. This also does not prove an infinite path at a fixed natural j, does not prove any actual machine reachability, and does not refute a fuel bound depending on j (in particular the enormous root precision E-17). Future work should accelerate direct tails exactly and seek an index-dependent all-branches bound, rather than increase a uniform cutoff.

## Periodic cost words

Suppose an infinite ordinary path has an eventually periodic cost sequence. Discard the finite prefix and choose its primitive period d_0,...,d_(ell-1). By the direct-only observation some d_i>=2. Put P_0=0, P_(i+1)=P_i+d_i, b=P_ell, D=2^b, B=sum_i 2^P_i, W=3b+ell.

By unrolling the edge recurrence over one period,

    D U_(k+1)=U_k+B S_k+C K_(S_k mod2),
    S_(k+1)=S_k+CW,

where U_k,S_k are measured at the cycle boundaries and K_s is an integer depending only on the boundary parity s. In particular

    K_0-K_1=sum_i (o_i(0)-o_i(1)) (2^P_(i+1)-2^(P_i+1)).

Each high edge contributes a signed sum of the distinct powers at positions P_i+1,...,P_(i+1)-1, disjoint from other contributions. The largest nonzero power dominates all lower powers. Therefore 0<|K_0-K_1|<D.

Write alpha=B/(D-1)=a/q in lowest terms. Since B has bit 0 set and at least one missing bit, a is odd and 0<alpha<1; q>=3 is odd. The binary repetend of alpha has exact bit period b, hence ord_q(2)=b. Indeed a shorter bit period would repeat the cyclic gaps between set bits of B and contradict primitivity of the cost word. (Reading the repetend in the opposite direction only reverses these gaps.)

For fixed parity, the affine recurrence has a particular solution U=alpha S+C beta_s with rational beta_s. If W is odd, take two periods at once to solve for the two parity-specific intercepts. The homogeneous error decays by D^-1 per cycle. Since U is integral and the particular solution has a fixed rational denominator, this error must eventually be zero: a nonzero error strictly smaller than the reciprocal of that denominator cannot separate an integer from the particular solution. It then was zero at the start of the periodic tail as well. The resulting one- or two-period drift, respectively alpha CW or 2 alpha CW, is integral. Since q odd,

    q | CW.                                                (1)

If W is even, U mod2 = S mod2 is unchanged after one period, so

    k=CW/q is even.                                       (2)

Here a is odd and U increases by ak.

If W is odd, unroll two periods and reduce the exact drift equation modulo D+1. The B S terms cancel, D=-1 modulo D+1, and B+2alpha=(D+1)alpha. Since alpha CW is integral by (1), the result is

    D+1 | C(K_0-K_1).                                    (3)

Consequently any odd-W period requires gcd(C,D+1)>1.

## Exclusion for C=1; restrictions for C=211

First, if W is even and q|W, then 3b<W<=4b<4q, because b=ord_q(2)<=phi(q)<=q-1. W is even and q odd, so W=2q. It follows that b>q/2. The divisibility b|phi(q) forces b=phi(q). An odd q with two distinct prime factors has ord_q(2)<=phi(q)/2 (the two prime-power group orders are even, and their least common multiple is at most half their product). Therefore q is a prime power. But phi(q)>=2q/3 for odd prime powers, yielding W=3b+ell>2q, a contradiction.

For C=1, (1) applies with q|W and (3) is impossible when W odd. Thus an infinite ordinary C=1 shadow path with U,V>2 has no eventually periodic cost word. This is aperiodicity, not mortality.

For C=211 (prime), odd W could only occur if 211|2^b+1 by (3). The multiplicative order of 2 mod211 is 210 (check the prime divisors 2,3,5,7 of 210), so b=105 mod210 is odd. In that case 211 does not divide q, and (1) implies q|W. For odd b, the quotient phi(q)/b is even. If b<=phi(q)/4, then W<=4b<q. Otherwise b=phi(q)/2, and q must be a prime power: with two distinct odd primes, the odd part of phi(q) is at most phi(q)/4, and b divides it. For a prime power this gives W>q, since 3phi(q)/2>=q, and W<2q, again impossible if q|W. Thus every possible eventually periodic cost word in a root32 shadow has even W and 211|q.

There is another constraint using S=5 mod211. With h=(D-1)/q and k=211 W/q, substitute U_(1)=U_(0)+ak into the one-cycle equation and reduce modulo211. As D=1 mod211, B=ah and 211 does not divide a, obtain

    k=5h mod211.                                         (4)

The case 211|h implies 211|k, hence q|W, already impossible. Therefore v_211(D-1)=v_211(q)=e>=1. The elementary prime-power lifting law v_p(A^m-1)=v_p(A-1)+v_p(m) for odd p|A-1 follows by the binomial expansion for m=p, followed by the geometric sum when p does not divide m. Here (2^210-1)/211=109 mod211, so b=210*211^(e-1)*d0 with 211 not dividing d0. Since q=211^e*m, (4) yields

    W/211^(e-1) = 123 d0 mod211,
    ell/211^(e-1) = 126 d0 mod211.

Indeed h=109 d0/m mod211 and k=W/(211^(e-1)*m), and 5*109=123 mod211, 3*210=208 mod211. In particular the bit period cannot be balanced (ell=b/2 would give ell/211^(e-1)=105 d0 instead). Thus every remaining periodic candidate has an unbalanced binary repetend, even W, 211|q, (1), (2), (4).

## Reproducible finite census

ShadowPeriodicDenominators.cpp enumerates every odd denominator divisible by 211 up to a user-specified bound, and each multiplicative-by-two orbit of reduced numerators. It uses the period length b and number ell of one digits (the number of orbit representatives x with 2x>=q). It tests W even, (1), (2), (4). For bound 700000 the run returned candidates=73, pass=0, qwithpass=0. This is a necessary-condition test only; it does not assert that any surviving candidate would give an admissible shadow path. No conclusion is drawn for denominators above the bound.

Build with a C++17 compiler supporting unsigned __int128, then run the executable with argument 700000. Neither this bounded census nor the paper argument proves an upper bound on the cost of an aperiodic path. The actual missing universal theorem is an index-dependent bound that fits the exact root precision E-17, or another exclusion argument for all remaining j.
