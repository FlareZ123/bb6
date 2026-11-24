# Density-zero residuals for Machine C dyadic inverse-cone certificates

**Status:** new paper-level theorem, using the existing source-certified all-depth ordinary inverse grammar and large-right modular lifting law. No new kernel-certified density theorem is claimed yet. This proves a density-zero bound on the *indices not excluded by the certificate method*, not a Machine C blank-root decision or BB(6) upper bound. The decisive new ingredient is an arbitrary-multiplicity collision construction, rather than a finite residue census.

## 1. Signed inverse coordinates

Write an actual section target as (x,y), and signed shadow counters as U=-x, V=-y (or congruent signed representatives). Put S=U+2V, p=S mod 2, Z=(U-2-p)/2. These definitions use integer arithmetic, and Z is integral since U and S have the same parity. The ordinary inverse edges in the large-right region have a bit cost r: r=1 for direct, r=n+2 for a high-bounce edge of depth n. The exact normalized recurrence is

    S' = S+3r+1,
    p' = S' mod 2,
    2^r Z' = Z+(S+p)/2+1-p'.             (1)

The ordinary edge is compatible precisely when its right-hand side is divisible by 2^r. Indeed, put o=(U+V) mod 2 and Q=U+V-o. Divisibility modulo 2 first forces p'=o, hence r mod 2=(V+1) mod 2; the right side of (1) is then Q. For r=1 this is the direct edge (V even); for r>=2 it imposes r<=v2(Q) and the correct high-bounce parity. In U,V coordinates the children are

    direct: U'=U+V+2, V'=(V+2)/2;
    high:   U'=Q/2^(r-1)+2+o, 2V'+U'=S+3r+1.

These are exactly the negatives of the ordinary inverse equations, not an assumed dynamics for exceptional small source states. The source-certified [ModularCone](../im-results/agent42-modular-cone/ModularCone.lean) and [ModularConeSource](../im-results/agent42-modular-cone/ModularConeSource.lean) use the same equations with positive-counter residue orientation. Their Large(b,y): 3*2^b<=y+2 condition propagates along every covered inverse edge, and exact valuation below b excludes the exceptional pure-power cases.

## 2. Exact affine binary branch population

An affine state at a binary parameter prefix has S=s+sigma*t and Z=z+lambda*t, with sigma divisible by 4 and lambda odd; the unread parameter t ranges over integers. Any prescribed cost r is compatible on exactly one residue class of t modulo 2^r, since the slope of the right side of (1) is lambda+sigma/2, which is odd. On restricting to that class, t=a+2^r*t', the new Z slope is still odd and the S slope becomes 2^r*sigma. This gives the same assertion for every finite cost word: there is one compatible prefix of length equal to its total cost.

For counting *all* competing words, process parameter bits one at a time, retaining histories with multiplicity, even if configurations coincide. There are two active types after the initial bit:

- C: a completed word paired with the pending possibility of extending its last gap by two or more bits;
- A: a partially completed gap with its next permitted endpoint one bit away.

Give a C pair weight 2 and an A weight 1. A root with no previous gap is treated separately (its expected weight after one bit is 3/2).

For C, use U=2Z+2+p. On reading the next bit, exactly one bit value chooses the odd-cost new gap r=1, producing a C pair; the other chooses the even-cost new gap r=2, producing an A candidate. Independently, extension of the previous gap survives this bit precisely if U-2-p is divisible by 4, producing another A. This is true on exactly one bit value. In the new-even case the candidate future U is (U+S-2(1-p))/4+2+(1-p), with future S=S+7; in the extension case it is (U-2-p)/4+2+p, with future S=S+6. These are integral once the first-bit constraint is imposed. At an A state the future candidate U has odd affine slope, so exactly one next bit gives U parity equal to its future S parity and completes a C pair; the other kills it. The C U slope is twice an odd integer, and both A slopes are odd after the bit substitution. Thus these assertions continue at every prefix.

Consequently the total weight N satisfies

    N(prefix 0)+N(prefix 1)=2*N(prefix).

The initial expected weight is finite, and the empty population is absorbing. This is an integer martingale on the fair binary prefix tree. Counting histories with multiplicity is essential for the equality. The process is exact for the ordinary congruence grammar; incomplete gaps are retained until disproved, so zero width is a complete finite exhaustion, not a depth cutoff.

## 3. Duplication identity and arbitrary amplification

The crucial observation is that two distinct words of the same total cost and length have the same final affine mass, and can be made arbitrarily close in their final normalized left coordinate.

Start at even S and put c=S/2+1. Odd r preserves even parity. For the two words A=(1,3), B=(3,1), equation (1) gives

    16 Z_A = Z+3c+4,
    16 Z_B = Z+9c+40,
    S_A=S_B=S+14.

The numerator difference is 6(c+6). If S=-14 (mod 2^(L+4)), then c+6=0 (mod 2^(L+3)). Both words therefore have exactly the same compatible four-bit prefix, and their resulting Z values agree modulo 2^L for every unread parameter value. Intermediate divisibility follows from the final divisibility, because the later summands have the corresponding earlier power-of-two factors.

Two affine states with the same S(t) and Z values congruent modulo 2^L have identical compatibility for **every** word of cost <=L: the unrolled right sides of (1) differ by the initial Z difference. This synchronization is exact for all parameter values in the common prefix.

Any C state can be steered to the required collision mass uniformly in its coefficients. First follow L+4 direct costs r=1 (each word is feasible on its unique cylinder); the remaining S slope is divisible by M=2^(L+4). Now choose q in [0,M-1] such that S+7q=-14 (mod M), and follow q copies of r=2. Since 7 is odd and the S slope is a multiple of M, the desired residue holds for every unread parameter. Steering takes at most L+4+2(M-1) bits.

Define F(0)=0 and

    F(k+1)=2F(k)+6+2^(F(k)+5).

Induction proves that from any C state there exists a bit extension of length <=F(k) with at least 2^k completed descendants. For the step, use L=F(k), steer to the collision mass, realize the common four-bit prefix for A and B, and apply the induction hypothesis to A. Synchronization transfers every descendant word to B, and the initial two words distinguish the histories. The total cost is at most L+4+2(M-1)+4+L=F(k+1). From any A state first complete it on its one matching bit.

This is a uniform amplification theorem: from any nonempty population, for every finite threshold B there is a bit extension of length bounded solely by B on which N reaches at least B. No assumption of eventual periodicity, independence of branches, or empirical mortality is used.

## 4. Extinction in density

For a finite binary tree, stop the population at the first prefix with N=0 or N>=B. The stopped expectation is the initial expectation by the one-step averaging identity. Therefore the proportion of prefixes that have ever reached B is at most E[N_initial]/B.

On prefixes still nonempty and below B, choose k with 2^(k+1)>=B and H=F(k)+1. By amplification, among their length-H extensions at least a fraction 2^-H reaches B (or is already stopped). The proportion remaining live and below B after h such blocks is at most (1-2^-H)^h. Hence the proportion of nonempty populations at precision j is bounded by

    E[N_initial]/B + (1-2^-H)^floor(j/H).

Let j tend to infinity, then B tend to infinity. The fraction of parameter residues with nonempty ordinary inverse branch population tends to zero. This is an elementary finite counting proof; no probability-limit theorem is required. The bound is very weak quantitatively because F grows rapidly, but it is uniform in the affine coefficients subject to the two slope conditions.

## 5. Application to the necessary low-stop ray

Use the existing source-certified reduction [LowRayFullFan](../im-results/agent13-residual-frontier/LowRayFullFan.md) and [NegativeShadow](../im-results/agent13-residual-frontier/NegativeShadow.lean): m=512z+67, T=1024z+129, u=2^T-6z-1, rectangle target (180u+28,166u+25), with positive negative-shadow representatives

    U=1080z+152, V=996z+141,
    S=3072z+434, Z=540z+75.

Here r must be even, and the first r=2 is compatible identically since the recurrence numerator is 4(519z+73). At total cost 2 there is exactly one C pair (including all longer even initial gaps):

    S=3072z+441, Z=519z+73.

The S slope is divisible by 4 and the Z slope is odd. The population starts at weight 2 with all bits of z still free. Thus the fraction of z residues with nonempty width after j further bits tends to zero.

If width is zero at fixed total precision P=j+2, all possible ordinary inverse paths have exhausted at smaller cost, including the longer-gap possibilities. At each visited node the selected numerator Q has valuation strictly below the remaining precision; otherwise a pending or completed gap would survive. Each terminal leaf has no ordinary edge, so V is odd and (U+V) mod 4 is 2 or 3: the original odd-image forbidden region after negation. All visited positive shadows have mass at most 3072z+434+4P, since each edge adds 3r+1<=4r. For sufficiently large z (with P fixed), the available precision T minus spent cost exceeds log2(2*(3072z+434+4P+8))+1 and exceeds every required valuation. Hence the existing sound NegativeShadow checker has a finite successful certificate (fuel at most P+1) for every such z. The finite exceptional initial z values do not affect density.

For every fixed P the zero-width condition is a union of residue classes modulo 2^(P-2). Their complement proportion tends to zero as P tends to infinity. Therefore the set of z for which **no finite negative-shadow certificate fits the prescribed 1024z+129 bit budget has upper natural density zero**.

## 6. High-stop extension using the large-right checker

In the unified original parameterization, let j>=1,m>=0 and k+j+3m+4=2^(2m+2)(j+2). At the actual target (2j+1,k) take exact signed shadow U=-(2j+1), V=-k. Then

    S=6m+7-2^(2m+3)(j+2), Z=-j-2.

For each fixed m the affine parameter j has S slope divisible by 4 and Z slope odd, uniformly in m. Start with the root with no last-gap continuation; after one bit its two possible populations have weights 2 and 1. The same extinction-in-density argument is uniform in m.

For a fixed prefix precision P with empty population, every selected numerator has exact valuation below its remaining precision, every ordinary branch terminates in the forbidden-image region, and no longer gap survives. The normalized signed child formulas are the negatives of ModularCone.direct/high. Congruence under each edge loses r bits, exactly as in the existing kernel. Choose source precision b=P+2, ensuring at least two bits at every leaf and enough bits for all exact valuation tests. The residue-normalized checker consequently accepts whenever its root Large(b,k) condition holds. To see HighValid explicitly, the selected numerator is divisible by 2^r; with r=n+2 this ensures the left quotient has the required parity, so the right quotient is integral. Changing a representative modulo 2^b preserves the valuation and these divisibilities, and the children agree modulo 2^(b-r). This is a finite induction over the exhausted word tree.

For every m>=0, k>=3j+4 (the linear exponential bound 2^(2m+3)>=3m+8 follows by induction). Therefore Large(b,k) holds for j>=2^b, uniformly in m. The fraction of j residues with nonempty width at fixed P tends uniformly to zero by the coefficient-independent bound in Section 4. It follows that the residual set of high pairs for which **no height-permitted finite modular certificate exists** has density zero in expanding square boxes, and indeed the upper row-density bound is uniform in m. The checker must be allowed unbounded adaptive precision; this claim does not hold for a fixed cap such as 32.

## Evidence and scope

The arithmetic collision and normalized recurrence were independently tested locally. The proof above is a paper derivation, not a new Lean source-closure claim. Existing source dependencies are the accepted ordinary inverse grammar, NegativeShadow soundness and ModularCone large-right soundness. The next formalization target is the affine word/collision lemma and finite binary-tree averaging theorem; the high-stop certificate pullback should be checked against the original module.

This is a property of a specific all-time exclusion method and its infinite parameter residual, not a proportion of six-state machines decided. Density zero does not imply the exceptional set is empty. The exact Machine C halting criterion still requires eliminating every residual low and high parameter or exhibiting an actual blank-origin halt. No exact BB(6) value or improved attainable lower bound is claimed.
