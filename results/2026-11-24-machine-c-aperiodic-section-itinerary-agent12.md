# Aperiodicity of infinite Machine C section orbits

**Theorem (Agent 12, 24 November 2026).** No infinite successful orbit of the exact Machine C section map has an eventually periodic complete branch itinerary. The complete label records the outer case, the exact recursive bounce depth and middle parity, and the ordinary versus exceptional exit. This is conditional on infinitude, and does not decide blank halting. It is a mathematical paper proof using [the actual section equations](../im-results/agent46-c-jump/FastSectionDef.lean) and [bounce recursion](../im-results/agent46-c-jump/BounceCalc.lean). Supporting [Lean arithmetic](../im-results/agent12-c-high-shadow/AffinePeriod.lean) checks the affine increment lemma and final modular contradiction, not the entire number-theoretic classification.

## Exact affine equations

Write A=a, M=a+2k. Every successful edge increases M by at least two ([source theorem](../im-results/agent3-c-bounce-inverse/SectionMassStrict.lean)). After the first edge k>=1. The finitely many bounded special inputs cannot recur infinitely. An a=0 or a=1 bounce starts with fixed middle counter K=1 or K=4; for any fixed depth the middle counter K_n, and hence output x+y, is fixed by its label, including the exceptional exit. Thus repeated occurrences of any fixed such label would have bounded output mass, contradicting strict mass growth. An eventually periodic tail therefore has a>=2,k>=1 throughout.

The direct case a>=2k outputs (a-2k,2k+2), giving A'=2A-M, M'=M+4, shift r=1.

Otherwise start the bounce with K=a-1,c=2k-a+3. Put o=a mod 2. For odd K a recursion sends (K,c) to (2K+3,c-2K-3); for even K it sends it to (2K+4,c-2K-5). Both preserve middle parity and increase c+2K by 3. After n recursions, odd K satisfies K_n+3=2^n(a+2), even K satisfies K_n+4=2^n(a+3). With r=n+2, the ordinary odd-middle exit (2K_n+6-c_n,c_n) and ordinary even-middle exit (2K_n+8-c_n,c_n-1) both give

    x+y+o = 2^(r-1)(a+2+o)
    M' = M+3r+1
    A' = 2^r(A+2+o)-M-(3r+1)-2o.

Here c+2K=M+1 initially. The exceptional even-middle exit c_n=4 gives (2K_n+2,3), so x+y=2^(r-1)(a+3)-3, M'=M+3r-1 and A'=2^r(A+3)-M-(3r-1)-6. These exhaust successful large-input branches. Each has the form A'=2^r A-M+b, M'=M+w with integer constants fixed by the label, r>=1,w>0. Ordinary edges, including direct, have w=3r+1.

## Repeated words force affine growth

Compose a repeated word of L labels with shifts r_1,...,r_L:

    A'=P A-Q M+C, M'=M+W,
    R=sum r_i, P=2^R,
    Q=sum_i 2^(r_{i+1}+...+r_L).

Q is odd, with L one-bits, 0<Q<=P-1; equality iff all shifts are 1. At block boundaries M_t=M_0+tW and 0<=A_t<=M_t. For D_t=A_{t+1}-A_t, E_t=(P-1)D_t-QW, subtract consecutive affine equations to obtain E_{t+1}=P E_t. The linear bound on A gives a linear bound on |E_t|, so P>=2 forces E_t=0. Consequently

    (P-1)(A_{t+1}-A_t)=QW.                       (1)

If any exceptional exit recurs, rotate the word to start just after it; then A_t=M_t-6 at each boundary. Equation (1) gives Q=P-1, contradicting the exceptional shift r>=2. An all-direct tail decreases a by 2k>=2 at each step, so cannot be infinite.

## Binary repetend of the primitive mixed ordinary word

Take the least shift period r_1,...,r_L, with W=3R+L. Since a mod 2=M mod 2, its parity labels repeat after one word if W is even, two if odd. Repetition twice leaves Q/(2^R-1) unchanged. Reduce this fraction to u/d. Its denominator d is odd, d>=3, and (1) implies d divides W (if applied to two words, use oddness of d).

The binary repetend of u/d consists of the R bits of Q with leading zeros. It has least period R: the one-bits at positions 0,r_L,r_L+r_{L-1},...,R-r_1 have cyclic gap sequence the reversal of the primitive shift word, and a smaller binary period would repeat those gaps. Thus R=ord_d(2). Let H=<2> in the units modulo d and C=uH. Binary long division visits the R residues in C, producing a 1 exactly above d/2, so L counts the upper-half residues of C. We have 1<=L<R and

    d | (3R+L),   d<=3R+L<4R.

Since R divides phi(d)<d, h=phi(d)/R<=3.

## Denominator classification

If -1 belongs to H, reflection pairs upper and lower residues, giving L=R/2 and d|7R. For the largest prime factor p of d of exponent e, the p-adic valuation of R is at most e-1: R divides the lcm of all prime-power totients and smaller primes q contribute no factor p through q or q-1. Thus p=7, but powers of 2 mod 7 are {1,2,4}, not -1. Contradiction. Hence -1 has order two in the quotient unit group by H; h is even and therefore h=2.

If d has s distinct odd prime factors, the product of their totients has 2-adic valuation at least s-1 more than the lcm. Thus 2^(s-1) divides phi(d)/R=2, giving s<=2. If d=p^e, then R=phi(d)/2, 3R>=d, and d<3R+L<4R<2d, impossible. So d=p^e q^f with 3<=p<q. Again d<=W<4R<2d, whence W=d and 3R<d. If p>=5,q>=7, then 3R/d=(3/2)(1-1/p)(1-1/q)>=36/35>1. Therefore p=3.

Set t=3^(e-1)q^(f-1), odd. Then d=3qt,R=(q-1)t,L=3t. The reduction of units to mod d0=3q is surjective with odd kernel of order t, contained in index-two H. Its image H0=<2> also has index two and C is the full preimage of C0. Each v in C0 has t lifts v+j d0, exactly (t-1)/2 above d/2 plus one iff v>d0/2. Hence, with L0 the upper-half count of C0,

    L0=(q-1)/2 + t(7-q)/2.                       (2)

For q=5,t>=3 gives L0>=5, exceeding q-1=4, so t=1. For q=7 equation (2) gives L0=3, but the two cosets mod 21 have counts 2 and 4. For q>=11,t>=3 gives L0<=-1, so t=1 and L0=3. In this last case every lower-half v>=3q/4 maps injectively by doubling to the upper half. Thus at least q-7 members are units below 3q/4. Their number is floor(3q/4)-floor(q/4)<=(q+1)/2 (no multiples of q). Consequently q<=15. For q=11, 2^5=-1 mod 33, impossible. For q=13 the cosets mod 39 have upper-half counts 4 and 8, neither 3. For q=5 the cosets mod 15 have counts 1 and 3. Representatives for the two cosets at d=15,21,39 are (1,7),(1,5),(1,7), respectively; the corresponding orders are 4,6,12, and the second representative is not in the first orbit.

Only d=15 remains, with R=4,L=3. Thus the primitive mixed shift word is, up to rotation, (2,1,1).

## Sole candidate eliminated modulo 17

Rotate to ordinary depth-zero bounce followed by two direct edges. At block start o=A mod 2. The equations above give

    M'=M+15, A'=16A-7M-21+8o.

Parity flips, so two blocks yield M''=M+30 and A''=256A-119M-454+120o. Equation (1) now forces A''-A=119*30/255=14, hence

    255A=119M+468-120o.

Both 255 and 119 are divisible by 17. But 468-120o is 9 or 8 modulo 17 for o=0 or 1. Contradiction. QED.

This proof has no finite period cutoff. It rules out complete repeating affine-word growth proofs, not nonperiodic infinite trajectories, more general invariants, or finite halting paths. It neither supplies a blank-orbit infinitude proof nor changes the known BB(6) bound.
