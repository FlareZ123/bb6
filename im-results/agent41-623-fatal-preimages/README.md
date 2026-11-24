# Exact parameter-level inverse of the #623 synthetic three-return halters

## Claim and scope

For even p >= 8 define x=(3^p-5)/2, y=(13*3^p-4*p+7)/2, and k=p-1. These are Agent22's synthetic three-return halters (m=p-2), from [Agent22ThreeStepSource.lean](../agent22-623-robust-band/Agent22ThreeStepSource.lean), pinned source CI 42640823077. They are not known to occur on the blank-root orbit.

This note derives the **complete even-first immediate predecessor set** of D(x,y) using two digit-count equations whose inputs are O(p), rather than O(3^p). In particular the lower asymptotic density of even exponents with no even-first predecessor is at least 1/3. By the original-source even-first invariant these members cannot be visited from blank. This is a partial exclusion of a synthetic halting family, not a #623 or BB(6) decision.

The digit identities and their specialization to the existing exact drain arithmetic are kernel-checked locally; the complete predecessor and density arguments below are mathematical derivations using the existing source theorems, not yet an end-to-end Lean theorem. Retain under im-results.

## Parameter theorem

Let B_k=(13*3^k-1)/2. For t>=0 let N1,N2 be counts of ordinary ternary digits 1,2; let P,M be counts of balanced ternary digits +1,-1. Leading zeros do not matter.

The full list is the union of the following two possibilities.

* LE: solve p=3t-1-2N1-N2 for 0<=t<=p+1. Set b=B_k-2t-1 and A=x-(p-4-2N1-2N2). The parent is D(A+b,b-2).
* RO: solve 3p=3t+P+2M+1 for 0<=t<=p. Set b=B_k-2t and A=x+p-1-2M. The parent is D(b+1,A+b-3).

Each scalar map is strictly increasing. Thus there is at most one parent per sector. Parameter existence is computable by binary search using O(log p) digit-count evaluations, each O(log p) small integer operations, with no construction of 3^p needed unless the coordinates are requested.

## Proof of completeness

Use the original-source inverse window and positive-trace results in [InverseWindowSource.lean](../agent49-parity623/InverseWindowSource.lean), and the generic arithmetic in [DrainCorrectionGrowth.lean](../agent49-parity623/DrainCorrectionGrowth.lean). Write n=1+floor(log2 y). A successful drain producing D(x,y) satisfies A<=x+n, x<=A+n, z+3b<=y<=z+3b+4n. Here y<2^(2p+3) and x>=4p+6, hence x>=2n. Consequently every successful drain for this target is a positive-budget trace with exact output x=A+J(b), y=z+3b+E(b), where E is even.

The exhaustive ParentEnvelope rules out axis outputs (y=7 or 14) and the zero-first diagonal drain (A=0 would force x<=n). The four remaining branches with even-first parent have (b parity,z): LO=(even,5), LE=(even,2), RO=(odd,3), RE=(odd,0). As y is even for even p, only LE and RO remain. In both cases y=3B_k-2p+5, and the odd k implies odd B_k. Put j=B_k-b. The image equation gives 3j=2p+E(b)+z-5, so 0<=j<4p+4 by the inverse window. Thus LE requires j=2t+1 and RO j=2t, with t<3^k and 2t<3^k respectively (p>=8).

The following exact identities are proved by induction in FatalFamilyInverseArithmetic.lean and instantiated with the actual existing excess/drift in FatalFamilyInverseActual.lean:

    E(B_k-(2t+1)) = 8+4N1+2N2
    J(B_k-(2t+1)) = k-3-2N1-2N2       (t<3^k)
    E(B_k-2t) = 4k+4-2P-4M
    J(B_k-2t) = -k+2M                 (2t<3^k)

For odd offsets, stripping an ordinary digit 0,1,2 adds (0,+1),(4,-1),(2,-1) to (E,J). For even offsets, stripping a balanced digit 0,+1,-1 adds (4,-1),(2,-1),(0,+1). Base B_0=6, with E(5)=8,J(5)=-3 and E(6)=4,J(6)=0.

Insert the identities in the output equation and solve for p; the first-coordinate equation determines A. The ordinary weighted digit sum 2N1+N2<=2t, and the balanced weight is nonnegative, give the stated search bounds.

Conversely any t satisfying an equation in the search range obeys the requisite digit-length bounds. Since |J|<=p+2, A=x-J>=n. The third-coordinate identity gives b<2^n since E>=0 and z>=0. The source positive-trace existence theorem produces a successful drain whose coordinates are forced to be x,y by trace_image and trace_drift. LE has b,A even; RO has b,A odd. All reconstructed parents have even first counter and lie in their prescribed branch (A>=n>0, b large). This proves both inclusions.

Strict increase: on adding one to ordinary t, trailing 2s reset to 0 and the first changed non-2 digit raises 2N1+N2 by at most 2. For balanced t, trailing +1 digits become -1 (weight P+2M rises by 1 per digit), and the next digit changes from -1 to 0 or 0 to +1, so the weight drops by at most 2. In both cases the increase of the linear term 3t dominates. Leading zeros are allowed.

## Density bound (paper proof)

For LE, p(t)=3t+O(log(t+2)); the even-p condition is N1+N2 odd, since t mod 2=N1 mod 2. The parity of the number of nonzero ternary digits has asymptotically equal frequencies: over a complete block of 3^h low-digit words the signed difference is (1-2)^h. A general initial interval is partitioned into aligned 3^h blocks plus a partial block, with h chosen so 3^h is of order sqrt(interval length); the fixed high-digit parity only changes the sign. Hence the even-p LE count through X is X/6+o(X).

For RO, p(t)=t+O(log(t+2)), when integral. Integrality and evenness are equivalent to P+2M=2 mod 3 and M odd, by t mod 2=(P+M) mod 2. Balanced ternary low words of h digits fill the centered intervals of length 3^h, with fixed higher digits. The pair of digit contributions in Z/3 x Z/2 is (0,0),(1,0),(2,1). Every element occurs in some word of length 3, so convolution by the uniform length-3 word distribution has a uniform component of weight at least 6/27; its remaining component is a probability distribution. Repeated independent blocks converge to uniform, with discrepancy bounded by (7/9)^floor(h/3). The same initial-interval partition, allowing two end fragments, gives asymptotic 1/6 frequency for the required pair. Thus the even-p RO count through X is X/6+o(X).

The union of the two sets has size at most X/3+o(X), while the number of even exponents is X/2+O(1). At least 1/3 in lower density have neither predecessor. The original blank-root section D(0,7) differs from every target here, and every previous section state of a reachable target must have even first counter (Agent49ParitySource.run_preserves_even). The exclusion therefore applies to the authentic orbit.

## Reproduction and limitations

Lean 4.36.0-rc2 (b35cb10), using exact checked-in DrainCorrectionGrowth.lean blob ccdbb69e7e12b816f919289954f1e41ad67b47df from main commit 73fe7340da2b55535b61132443a712092fc3dde3:

    cp ../agent49-parity623/DrainCorrectionGrowth.lean /tmp/Agent49DrainCorrectionGrowth.lean
    cp FatalFamilyInverse{Arithmetic,Actual}.lean /tmp/
    cd /tmp
    lean -o Agent49DrainCorrectionGrowth.olean Agent49DrainCorrectionGrowth.lean
    lean -o FatalFamilyInverseArithmetic.olean FatalFamilyInverseArithmetic.lean
    LEAN_PATH=/tmp lean FatalFamilyInverseActual.lean

All exported proofs compile with only propext, Classical.choice and Quot.sound (some use fewer). No sorry or native_decide. No new pinned-source machine CI run was made for this note; existing source lemmas are referenced rather than re-proved.

Run python verify.py from this directory. It compares exact reconstructed parent sets to Agent49's existing complete inverse algorithm for 997 even exponents p=8..2000; the regression distribution is 435 with no parent, 442 with one, and 120 with two. The finite regression is not the proof of the asymptotic claim.

Next: formalize the complete source-envelope specialization and investigate deeper inverse ancestors of the surviving parameter families, ideally a parameter-level descent rather than more finite enumeration. The result does not exclude all possible terminal gates, or even the whole synthetic family.

## Explicit infinite missing-gate subfamily

For every integer r>=1, put p=6*3^r and k=p-1. Define L(t)=3t-1-2N1-N2 and R(t)=3t+P+2M+1. The maps are strictly increasing, even when the digit counts are truncated to any fixed length k. At the two adjacent integers t=2*3^r+1 and t+1 the ordinary counts are (1,1) and (0,2), giving L(t)=p-1 and L(t+1)=p+3. At t=p-3 and t+1 the balanced counts are (1,2) and (2,2), giving R(t)=3p-3 and R(t+1)=3p+1. Thus neither equation admits any natural t. This is a universal symbolic exclusion, not a bounded simulation.

[FatalFamilyWindow.lean](FatalFamilyWindow.lean) proves the exact family size/positive-budget hypotheses and necessary digit gates. [FatalFamilyInfinite.lean](FatalFamilyInfinite.lean) proves the monotonicity and the all-r missing-gate theorem without nonstandard axioms in Lean 4.36.0-rc2. [FatalFamilySource.lean](FatalFamilySource.lean) connects the gate to the unchanged-source root run (including theorem power_three_root_excluded). The source adapter passed a local signature-level type check; full pinned-source CI is still required. The initial focused run 45401674640 failed in the pre-existing Agent49 parent envelope because unrestricted simp normalized the two branch inequalities. The minimal repair is commit 1b34eeb6e4b546cd808824ed09c85aff2de8a371; the source proof conclusion remains pending the next actual CI result.

## Compressed inverse for arbitrary near-power targets

Write target counters as ((C*3^k+u)/2,(D*3^k+v)/2), C,D>0 and integral natural coordinates. For a block b=(D*3^h+w)/2, h>=1, the positive-budget recurrence strips one ternary level by

    r = (2*w) mod 3
    w' = (w+4*r-6)/3
    b' = (D*3^(h-1)+w')/2.

The associated (drift,excess) charges are (+1,0),(-1,4),(-1,2) for r=0,1,2. Since 3*abs(w')<=abs(w)+6, the residual contracts outside [-3,3]. It eventually hits one of three fixed residuals -3,-1,1, or the two-cycle -2,0. A fixed tail contributes a linear function of its length, and a full two-cycle contributes (0,2). [NearPowerDrain.lean](NearPowerDrain.lean) proves the exact recurrence, contraction, and universal fixed/cycle jump theorems using the actual existing drain statistics; all compile with standard foundational axioms.

For a guarded large-first target, n=2k+max(bitlength(D),bitlength(abs(v)))+2 bounds the true logarithmic inverse budget. The guard 3^k>=max(4n-u,30-v,1) ensures x>=2n and y>=15. For each eligible sector z, set h=k-1 and

    ceil((v-2z-8n)/3) <= w <= floor((v-2z)/3),
    w = 2*blockParity - D*3^(k-1) (mod 4).

Require 3^(k-1)>=max(1,8-w_lo), ensuring b>=4 throughout. Every possible block belongs to this interval by the source window; the exact image equation becomes v=3w+2(E(b)+z). Agent49's image step-two theorem permits binary search on that residue progression. From the unique block, A=x-J(b) determines the parent. The restored near-power coefficients are (3C+D,D) or (D,3C+D), and the offsets are obtained by the exact affine parent table. The actual positive-budget trace exists because b<2^n and A>=n using the true output budget, and b>=4 makes the reconstructed branch offsets valid. Parity filtering gives the full even-first list. If a sufficient guard fails, return unknown rather than asserting there are no parents.

[near_power.py](near_power.py) implements this arithmetic without constructing 3^k in the long-tail case; the guard uses bit lengths, and ordinary small-integer fallback is used when needed. Complexity per node is O(log(n+1)*(log(abs(w)+2)+log(D+2))) arithmetic operations, ignoring bit costs and allowing the direct fallback exponent to be O(log(abs(w)+2)). Thus for fixed reverse depth and the original near-power family the cost is polynomial in log p, rather than in p. The Python implementation itself is not kernel verified.

The local exact regression matched the existing inverse on 10,000 random drain-statistics cases and 1,000 random near-power targets (where the guard held). Every even p from 8 through 19,998 (9,996 values) had a closed finite reverse tree under this guarded algorithm, with maximum depth 23 at p=5,288 (34 nodes). The very large exponents 10^6, 10^9, 10^18 and 10^100 had no immediate even-first predecessor. These are finite computations from the mathematical algorithm, not all-p theorems or Lean-certified tree certificates. In particular, the max-depth observation is not a uniform bound.

The next useful task is a complete symbolic ancestor argument or a reusable source-sound inverse certificate checker; do not mistake the finite closure census for the solution of #623.
