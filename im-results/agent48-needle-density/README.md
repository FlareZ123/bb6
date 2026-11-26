# Computable natural densities of Space Needle terminal inverse histories

**New theorem:** the natural density of terminal exponents admitting any legal immediate predecessor exists and is computable. Its complement, exponents with no legal immediate parent, has density strictly between 0.566665 and 0.602053. At every fixed finite inverse depth the corresponding density likewise exists and is computable. Fixed-alphabet inverse histories have exponentially decaying density with depth. These are rigorous all-exponent statements, not sampled estimates. None determines authentic blank-root halting.

**Status:** period/spacing, exact order certificates (v=0..50), low hit lists, and arithmetic congruence iff sufficient size are local Lean 4.36.0-rc2 kernel results (standard axioms only). The real-limit/density arguments are paper proofs. Original-source adapter pending; underlying exact edge and valuation dichotomy accepted in [CI 42416997719](https://github.com/FlareZ123/bb6/actions/runs/42416997719). No external novelty claim.

## Period and tail theorem

The shifted counter b=d+2 has successful edge 2^v(2q+3) -> b+v+3(q+1), q>=0. For b'=2^K, the exact incoming edge equation is

    2^(K+1)+3 = D_v(2q+3)+2v, D_v=2^(v+1)+3.

For fixed v this is equivalent, beyond finitely many K, to 2^(K+1)=2v-3 modulo D_v: the quotient is odd and eventually >=3. Each v therefore has empty or one eventually periodic residue class of K modulo h_v=ord_(D_v)(2).

For m>=3 and t>0 with 2^t=1 mod D=2^m+3, the kernel-proved period theorem gives

    5m(m-3)<8t.

Write t=mq+r with 0<=r<m. Then D divides 2^r(-3)^q-1. Suppose 3^(q+1)<=2^(m-1). If r=0, q>0, and the residue (-3)^q-1 is nonzero of magnitude <D. If r>0, multiply by 2^(m-r): D divides (-3)^(q+1)-2^(m-r), nonzero odd of magnitude <=2^m. Both impossible. Thus 2^(m-1)<3^(q+1); since 3^5<2^8, 5(m-1)<8(q+1), giving 5(m-3)<8q. Multiply by m and use mq<=t. Two distinct hits of any fixed residue at a<b give a period b-a since 2 is a unit mod D.

Let A(N) count terminal exponents K in [1,N] with an incoming edge, and A_M(N) those with v<=M, M>=11. The [quadratic terminal dichotomy](../agent48-space-needle/NeedleTerminalDichotomy.lean) states that v>=11 implies either v^2<=8(K+1) or exact cancellation K+1=r(9^r+5), v=(9^r+3)/2, r>=1. There are O(log N) cancellation exponents. For M<v<=sqrt(8(N+1)), spacing gives at most 8N/[5(v+1)(v-2)]+1 hits per v. Therefore

    0<=A(N)-A_M(N)<=N T(M)+sqrt(8(N+1))+O(log N)
    T(M)=(8/15)(1/(M-1)+1/M+1/(M+1)).

The exact telescoping series is the sum of 8/[5(v+1)(v-2)] over v>M. The finite-union density delta_M exists, increases with M, and has limit delta. The displayed inequality squeezes A(N)/N to delta, with 0<=delta-delta_M<=T(M). For arbitrary epsilon choose M with T(M)<epsilon, compute the finite orders and residue classes (finite though potentially expensive), and combine by CRT/inclusion-exclusion. This gives effective computability.

## Explicit interval

The exact low-v hits, in (v, K residue, period) notation, are (0,0,4), (2,9,10), (3,12,18), (5,22,66), (6,13,130), (8,98,204); v=1,4,7,9,10 have no hits. Their union density by exact generalized CRT inclusion-exclusion is 87067/218790=0.397947803830... . For v=11..50 use the conservative sum of reciprocal exact orders 0.0033784949329... regardless of offset solvability. T(50)=29996/937125=0.032008536748... . Thus

    0.397947803830...<=delta<=0.433334835511...,
    0.566665164488...<=1-delta<=0.602052196169... .

No-parent density exceeds 56.6665%. Exact rational checks in density_certificate.py. The Lean order checker certifies the period, full prime factor list, primality by trial division, and nonperiod at r/p for each prime factor. This proves exact least order and needs no external factoring oracle.

## Every fixed inverse depth

Let A_d be exponents K>=1 admitting a legal backward path of length d. For every fixed d>=1, A_d has computable natural density. Use the [all-depth affine inverse](../agent20-needle-coprime/TerminalAffine.md), source gate [45355182778](https://github.com/FlareZ123/bb6/actions/runs/45355182778).

Fix an inverse prefix w=(m_1,...,m_j), m_i=v_i+1. The symbolic node, whenever legal, is

    2Lb=2^n+d0, n=K+1+S,
    L=prod_i(2^m_i+3), S=sum_i m_i, d0 even and d0<2L.

The constants depend only on w. A next index m requires, and with an odd quotient >=3 is equivalent to,

    L(2^m+3) | 2^n+C, C=d0+L(5-2m).

For fixed m this restricts K to one residue class modulo ord_(2^m+3)(2) or empty. For K<=N each legal inverse node decreases strictly and the new source is >=3*2^(m-1), so m<K<=N. Put H_N=1+floor(log2(|d0|+L(2N+5))), whence |C|<2^H_N and H_N=O_w(log N). By the rotation dichotomy, either m^2<(H_N+2)m+2(N+1+S) or m|n and C=-(-3)^(n/m). Ordinary m satisfy m<H_N+2+sqrt(2(N+1+S)), so there are O_w(sqrt N+log N) possibilities. Exceptional m>=4 gives C<0, k=n/m positive even, and

    2Lm=d0+5L+3^k.

Since 3^k=|C|<2^H_N, k<H_N. For each k at most one m and hence one K=mk-1-S is possible. All exceptional high extensions contribute O_w(log N) exponents. The same telescoping sum bounds upper density of exponents admitting the fixed prefix followed by m>M+1 by T(M); finite-N terms can depend on w.

For a fixed full word all affine divisibility tests have fixed odd moduli and offsets, and positivity of every quotient holds eventually. Thus word legality is eventually periodic. Given epsilon, choose a first cutoff with T(M)<epsilon/d, then at the next depth choose a cutoff such that the number of retained prefixes times T(M')<epsilon/d. Continue d levels. The finite bounded-word union has rational density; every excluded exponent has some legal path with a first index outside its assigned cutoff. The union over those finitely many prefix tails has upper density <epsilon. Squeeze limsup and liminf to equality and compute density to arbitrary precision. This is not uniform in d.

## Fixed valuation alphabet: exponential depth decay

For alphabet 1<=m<=M let P_M be primes dividing its denominators. Put h_p=ord_p(2), s_p=nu_p(2^h_p-1). All p odd. For p^e|L, any positive period t modulo L satisfies p^max(0,e-s_p)|t: h_p|t, h_p|p-1, and by LTE nu_p(2^t-1)=s_p+nu_p(t). Multiplying gives

    ord_L(2)>=L/C_M, C_M=prod_(p in P_M) p^s_p.

The last affine test for each length-d word has density at most 1/ord_L(2)<=C_M/L. Sum over all words:

    density of legal depth-d histories using only m<=M
        <= C_M*(sum_(m=1)^M 1/(2^m+3))^d.

The ratio is <1 because each term <2^-m. This is exponential decay for fixed M. C_M is not uniform in M; exchanging these limits to claim zero unrestricted depth density is unjustified.

## Reproduction and next step

Run python3 unpack.py to reconstruct five exact hash-checked Lean files, compile NeedleOrderBound, NeedleOrderCert, NeedleOrderTable, NeedleTerminalDensityArithmetic, NeedleLowHits in order with current dir on LEAN_PATH. Run python3 density_certificate.py. Original-source spacing adapter NeedleTerminalDensitySource.lean is targeted by terminal-density in the existing manual growth workflow. The density theorems are paper proofs based on source-certified arithmetic, with their new arithmetic core locally checked. No all-time root or global BB(6) decision follows. Next: obtain a uniform unrestricted-depth density bound or a genuinely root-sensitive exclusion, rather than another finite scan.
