# Density-zero inverse reachability for Machine C

**Status (28 November 2026):** The entire original-source Machine C row-sparsity proof, low/high stopping-family corollaries, inverse-word extinction argument, and unchanged source parent law compiled together in Lean 4.36.0-rc2 in [run 46102569750](https://github.com/FlareZ123/bb6/actions/runs/46102569750) (80 modules). Final declarations `source_all_rows_sparse`, `source_low_sparse`, and `source_high_sparse` depend only on `[propext, Classical.choice, Quot.sound]`, without `sorryAx`. The later even-left/odd-right ray extension is not part of this accepted run. No blank-root decision or BB(6) upper bound is claimed.

## Main theorem (strengthened after the initial certificate-residual proof)

Let Reach(x,y) denote any section-reachability predicate satisfying the complete large-right parent law below (the actual Machine C predicate has that law). For every positive integer denominator d, there is one precision n such that:

- For every left counter x, all reachable right counters y with 3*2^(n+2) <= y+2 belong to a list of at most 2^n/d residues modulo 2^n. The modulus and height threshold do not depend on x.
- For the entire low stopping family y+3m+4=2^(2m+3), Reach(1,y) with m>=n+2 forces m into a list of at most 2^n/d residues.
- For every m, the high family y+j+3m+4=2^(2m+2)*(j+2), Reach(2j+1,y) with j>=2^(n+2) forces j into a list of at most 2^n/d residues. The same modulus works for every m.

Consequently the reachable section lattice has upper natural density zero in growing square boxes, the reachable low-stop indices have density zero, and the reachable high-stop parameter pairs have density zero, with a uniform row bound. Indeed, in any interval of length L, a residue cover of size r contains at most r*(L/2^n+1) integers, and the finite lower-height exception contributes a bounded number per row. Let L grow and then d grow. This is a restriction on actual reachable targets, stronger than a numerical census of certificate successes. It does not make the exceptional sets empty.

**Interpretation relevant to BB(6):** Since the blank-origin source dynamics are deterministic and terminate at their first stopping configuration, the set of *actually reached stopping states* is automatically of cardinality at most one. Thus density-zero of the low/high stopping-parameter sets, while formally correct, is not itself a useful nonhalting constraint. The genuinely structural result is the uniform sparse-cover theorem over *all* reachable section states in every fixed-left row, together with the general inverse-word extinction result; no particular stopping state is excluded by the density claim alone.

The checked declarations are in [DyadicRows.lean](../im-results/agent21-c-shadow-density/DyadicRows.lean) and [DyadicStops.lean](../im-results/agent21-c-shadow-density/DyadicStops.lean), using [DyadicReach.lean](../im-results/agent21-c-shadow-density/DyadicReach.lean) and [DyadicCover.lean](../im-results/agent21-c-shadow-density/DyadicCover.lean). The two one-line instantiations with the existing source parent law are in [DyadicSource.lean](../im-results/agent21-c-shadow-density/DyadicSource.lean).

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

Consequently, except for the empty-word initial state, the total weight N satisfies

    N(prefix 0)+N(prefix 1)=2*N(prefix).

At the initial state the corresponding inequality is <=. The formal argument uses the supermean inequality at every valid population.

The initial expected weight is finite, and the empty population is absorbing. This is an integer supermartingale on the fair binary prefix tree. Counting histories with multiplicity is essential for the equality. The process is exact for the ordinary congruence grammar; incomplete gaps are retained until disproved, so zero width is a complete finite exhaustion, not a depth cutoff.

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

For a finite binary tree, stop the population at the first prefix with N=0 or N>=B. The stopped expectation is at most the initial expectation by the one-step supermean inequality. Therefore the proportion of prefixes that have ever reached B is at most E[N_initial]/B.

On prefixes still nonempty and below B, choose k with 2^(k+1)>=B and H=F(k)+1. By amplification, among their length-H extensions at least a fraction 2^-H reaches B (or is already stopped). The proportion remaining live and below B after h such blocks is at most (1-2^-H)^h. Hence the proportion of nonempty populations at precision j is bounded by

    E[N_initial]/B + (1-2^-H)^floor(j/H).

Let j tend to infinity, then B tend to infinity. The fraction of parameter residues with nonempty ordinary inverse branch population tends to zero. This is an elementary finite counting proof; no probability-limit theorem is required. The bound is very weak quantitatively because F grows rapidly, but it is uniform in the affine coefficients subject to the two slope conditions.

## 5. Generalized admissibility and direct reachability bridge

The formal population model permits the weaker initial conditions

    sigma = 0 (mod 2), lambda + sigma/2 = 1 (mod 2).

For any nonempty positive cost word w, the coefficient of S/2 in its unrolled numerator is odd: it has the form 1+2^r*c for first positive cost r. Thus the parameter slope of that numerator is odd. Every candidate C or A in a one-bit transition is nonempty and positive. After completing any nonempty word, the affine mass slope becomes a multiple of four and its normalized Z slope is odd, giving the original stronger Good hypothesis required for the collision amplifier. The empty-word initial state can first complete the cost-one branch on its unique compatible bit. This proves extinction uniformly under the weaker Admissible condition.

Define OpenAt(S,Z,n) to mean either a compatible positive cost word of total cost n, or a positive word of total cost n+1 whose final cost is at least two and whose numerator is divisible by 2^n. The latter is the unfinished gap. The actual population contains exactly these completed and pending words. This exact characterization is proved by induction in DyadicPopulation.step_valid.

The parent law says that for reachable (x,y) with y>=8 and Q=x+y+(x+y)%2 of exact valuation v and Q>2^v, some reachable predecessor is either direct or high with cost r<=v. To prove that every reachable target with Large(n+2,y) has OpenAt:

- n=0: the empty word is compatible.
- If 2^n divides Q and n>0, select a single cost n of the correct parity or a pending cost n+1 of the correct parity. This gives OpenAt immediately.
- Otherwise v<n is the exact valuation. The height condition guarantees y>=8 and Q>2^v, so the parent law applies. The actual predecessor costs r<=n, preserves Large(n-r+2, predecessor-right), and satisfies recurrence (1). By induction its OpenAt at n-r can be prepended with r.

This is the Lean theorem DyadicReach.reach_open. It does not depend on any executable recursive exclusion checker's correctness. Congruence in S modulo 2^(n+1) and Z modulo 2^n preserves OpenAt (the accumulator difference is half the mass difference times its word coefficient). Therefore the binary-tree extinction bound directly gives a sparse residue cover of reachable targets.

## 6. Exact affine parameterizations

With x fixed and parameter y, S=-x-2y and Z=(-x-2-((-x) mod 2))/2 is constant. The slopes (-2,0) satisfy Admissible. This proves the entire row cover, uniform in x.

For the full low family x=1, y+3m+4=2^(2m+3),

    S=6m+7-2^(2m+4), Z=-2.

For fixed precision n and m>=n+2, the power term vanishes modulo 2^(n+1), and Large(n+2,y) follows from 3m+4<=2^(2m+2). The admissible affine root has slopes (6,0). This proves the full low family without needing to restrict to m=512z+67. It also implies relative density zero within that fixed arithmetic progression.

For the high family x=2j+1, y+j+3m+4=2^(2m+2)*(j+2),

    S=6m+7-2^(2m+3)*(j+2), Z=-j-2.

For fixed m the slopes (-2^(2m+3),-1) satisfy the stronger Good condition. Since y>=3j+4, the height threshold holds for j>=2^(n+2), uniformly in m. The uniform sparse cover proves the asserted result.

## Evidence and scope

[Formalization dossier](../im-results/agent21-c-shadow-density/README.md). Local Lean 4.36.0-rc2 accepts every abstract and parent-law-conditional declaration with only propext, Classical.choice, Quot.sound (reach_open itself does not need Classical.choice). No sorryAx. The authentic-source adapter is now accepted in run 46102569750: the exact source parent law, the uniform row theorem, and both stop-family consequences compiled in one dependency closure. The interface matches Agent42's source-certified parent law definitionally. The new ray theorem has a separate pending acceptance gate.

The original paper-level low-ray negative-shadow certificate argument and high modular-checker argument are preserved in Git history (initial paper commit 35adf89c86a7076451195e9c38de6eccc946211a). The direct reachability bridge above supersedes the need to rely on their implementation-level pullback. This is a structural infinite-parameter theorem, not a count of six-state machines decided. Density zero does not imply emptiness. No exact BB(6) value or improved attainable lower bound is claimed.
