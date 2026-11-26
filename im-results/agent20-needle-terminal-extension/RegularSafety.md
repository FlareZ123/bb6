# No regular binary inductive power-avoidance certificate for Space Needle

**Paper-level consequence of [terminal completion and mixed density](README.md).** Adapts the [Sheep regular safety proof of Agent 16](../agent16-sheep-automatic/NO-REGULAR-INVARIANT.md) to Space Needle. No conclusion about authentic halting.

## Statement

There is no nonempty regular language of canonical binary integers x>=3, disjoint from the powers of two, closed under the exact Space Needle successor F. Likewise there is no such language of even x>=4 closed under the first-even section E (one even step followed by the entire odd block, stopping at the next even counter). In particular neither kind of regular set can certify an infinite blank-root orbit. Regular languages here may use either bit order, since reversal preserves regularity. We use LSB-first words with canonical last digit 1.

## 1. A raw safety language must have bounded valuation

Suppose L is such a language, recognized by a complete finite DFA. Every member has a strictly increasing successor, so L is infinite. Let t be the transient length of the orbit of the initial DFA state under the digit 0. Choose a positive common period p of the zero action on all states and a common threshold T beyond which all zero runs are periodic.

If L accepts x=2^a u (u odd >=3) with a>=t, pumping low zeros shows that it accepts x_e=2^e u for arbitrarily large e=a mod p. The successor is

    F(x_e)=2^e u+e+c, c=3(u-1)/2.

For large e, the canonical low block delta=e+c has bit length ell much smaller than e, so its successor word has the bits of delta, then e-ell zeros, then the bits of u. Pumping this internal zero gap shows L accepts 2^b u+delta for any b=e mod p with both gaps at least T.

Let p_odd be the odd part of p, and J=lcm(p,ord_p_odd(2)), taking order 1 for modulus 1. For b sufficiently large and b=a mod J, the residue of 2^b u modulo p is constant. Choose 0<alpha<beta<2^(-T-1). For all sufficiently large such b and every delta=a+c mod p with alpha*2^b<delta<beta*2^b, the original e=delta-c is large and e-ell>=T; also b-ell>=T. Thus every sufficiently large integer in a fixed residue class mod p and an open subinterval of the phase window

    a+log2(u+alpha) < log2(x) mod J < a+log2(u+beta)

is accepted (read this as an interval on R/JZ, choosing an interior subinterval if it wraps). Indeed the phase window specifies a b in the progression, and delta=x-u*2^b satisfies the required inequalities and congruence. By mixed terminal density that cell contains prepared halters. Closure forces their terminal powers into L, contradiction. Hence every accepted valuation is <t. If t=0 the language is empty; otherwise write A=t-1.

## 2. Bounded valuation limits binary growth

For any forward-infinite counter set with all valuations v<=A along the raw trajectories, its number of n-bit starts is at most

    (A+1)*lambda_A^(n+A),

where sum_{m=1}^{A+1} lambda_A^(-m)=1 and 1<=lambda_A<2 (lambda_0=1). For each start take the first valuation word whose weight S=sum(v+1) is >=n; n<=S<=n+A. Exact cylinder uniqueness gives at most one start of n bits for each word, as the source residue modulo 2^S is fixed. The number of words of total weight S is at most lambda_A^S by the recurrence for ordered compositions (base count 1 at weight 0; absent negative terms). This proves strict sub-full binary growth. No probabilistic assumption about the actual orbit is used.

## 3. A finite phase-fibre argument forces full growth

For each DFA state q let H_q be the closed set of limiting log2 phases modulo 1 of unbounded accepted canonical tails starting at q. Consider the compact joint limit set of (x in Z_2, log2 x mod 1) as accepted x tends to positive infinity. For any low-bit infinite string z in Z_2, let H(z) be its phase fibre. The phase set obtainable with the first k bits of z fixed is exactly H_{q_k}, where q_k is the DFA state reached by that prefix: removing k fixed low bits divides by 2^k up to a bounded error, which vanishes in log phase. The joint fibre equals the intersection of this decreasing sequence of closed sets; the reverse inclusion follows by choosing successively large accepted integers with those low bits and approximating the desired phase. Since only finitely many H_q exist, the descending sequence stabilizes. Thus nonempty H(z) has only finitely many possible values.

Bounded valuations ensure every limit z has finite valuation <=A (the clopen cylinders partition the projection). On a fixed branch a the exact affine map is

    F_a(x) = r_a x + a-3/2,
    r_a=(2^(a+1)+3)/2^(a+1).

It is continuous on its 2-adic cylinder and asymptotically multiplies the real counter by r_a. Closure implies H(z)+log2(r_a) subset H(F_a(z)), and the image fibre is nonempty. Iterate any nonempty fibre. Two fibres repeat by finiteness; composing the inclusions gives a nonempty closed fibre containing its translation by log2 of a nonempty product of r_a's. That logarithm is irrational: the product has an odd numerator >1 and a power-of-two denominator. By density of irrational rotation the fibre is the entire circle.

Full phase implies every leading m-bit pattern (starting with 1) occurs in arbitrarily large accepted words: choose phases in the interior of each pattern's log interval. In LSB-first order, shorten the low prefix before that high pattern to a shortest path to the same DFA state, of length <=|Q|-1. The resulting word remains canonical and accepted. Distinct high patterns yield distinct shortened words, of lengths between m and m+|Q|-1. Thus the sum of the accepted counts over these lengths is >=2^(m-1), contradicting the strict growth bound of section 2. This proves the raw theorem. The bounded-valuation part of the obstruction (sections 2-3) is independent of terminal density and rules out any infinite eventually forward-closed regular set with uniformly bounded raw valuations.

## 4. First-even section

For an even nonterminal x, define y=F(x), h=v2(y-1). If y is even then h=0. For an odd nonterminal y the raw odd map satisfies F(y)-1=(5/2)(y-1). Thus the next even return is exactly

    E(x)=1+(5/2)^h*(F(x)-1).

The odd part of y-1 is positive odd; the finite block ends at an even counter. All raw states between even returns have valuation zero.

Suppose a regular even safety language is nonempty, closed under E and avoids all powers of two. First, if x=2^a u with a>=t, pump e as before. Choose a large e0=a mod p with e0+c-1>0; set h0=v2(e0+c-1). Restrict e=e0 mod P, where P=lcm(p,2^(h0+1)), and e>h0. Then h=h0 and

    E(x_e)=U*2^(e-h0)+delta_e,
    U=5^h0*u,
    delta_e=1+5^h0*(e+c-1)/2^h0.

The positive even delta_e range over an arithmetic progression with step d=5^h0*P/2^h0, an even integer. Internal zero-gap pumping again permits 2^b U+delta_e, with b=e0-h0 mod p and both gaps >=T. Restrict b to e0-h0 mod lcm(p,ord_d_odd(2)), large enough that 2^b U has fixed residue modulo d. The same small relative delta window as in section 1 yields an entire eventual residue-phase cell of even accepted integers. Prepared terminal density supplies a genuine even prepared halter in that cell, whose first-even orbit reaches its terminal power. Contradiction. Thus even source valuations are bounded by A=t-1; all intervening odd valuations are zero. Section 2 now applies to the even language itself, and rules out full limiting real phase (by the high-pattern shortening argument).

It remains to bound the odd-block length h on accepted even sources. If unbounded, select one fixed source valuation a with an unbounded sequence of h. Then accepted x approach the 2-adic singular point

    z_a=2^a(5-2a)/(2^(a+1)+3),

which solves F_a(z_a)=1 and has valuation a. Every finite prefix of its 2-adic digits has arbitrarily long accepted continuations. A rational with odd denominator has eventually periodic 2-adic digits: for numerator n and odd denominator D, the residual numerator updates as n'=(n-D*(n mod 2))/2, a bounded integer after a finite initial segment, so repeats. Choose infinitely many prefix lengths k=k0+jd with the same remaining periodic digit string and same DFA state. Fix one nonempty canonical accepted continuation from that state. Pumping these low prefixes gives accepted x_k=z_a+2^k B for a fixed positive rational B: if the periodic tail block has value V, its 2-adic value is V/(1-2^d), and the accepted high continuation contributes a positive integer. Hence F_a(x_k)-1=2^k r_a B, of valuation h=k+b for a fixed integer b. Its odd part is a fixed positive odd integer u (it is the genuine integer odd part for every large k). Their even returns are 1+5^(k+b)u, with phases dense mod 1 because d*log2(5) is irrational. Closure contradicts the strict growth consequence. Thus h is uniformly bounded.

Now the first-even map has only finitely many relevant affine branches (a,h); the conditions v2(x)=a and v2(F_a(x)-1)=h are clopen, and their slopes are 5^h*(2^(a+1)+3)/2^(a+h+1). Any nonempty product again has an odd numerator >1 over a power of two. Apply section 3 to E rather than F, obtaining full phase and the same contradiction. This proves the even theorem.

## Scope

These results exclude regular binary counter invariants under these two exact section relations, including ultimately periodic sets as a special case. They do not exclude nonregular sets, auxiliary history/certificates, all conceivable accelerations, a proof of unbounded valuations on the particular orbit, or TM-level proof systems that do not produce such a counter invariant. They do not assert anything about regular languages that merely contain the actual orbit without forward closure on all their members. The density result and phase-fibre arguments are paper-level and should be adversarially reviewed before any promotion; the exact inverse-path arithmetic and seed have separate Lean checks.
