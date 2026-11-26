# Exact reverse-block and prefix-only P1 carry exploration

**Scope and evidence.** This intermediate programme extends the exact-integer P1 critical-index computations beyond the earlier 7,593,750 cutoff, and develops an exact acceleration for both the modular and delayed carry relations. It is not yet a Lean numerical certificate, an all-index reset exclusion, a P1 decision, or a BB(6) bound. The original-source reductions are [BatchCarrySource](../agent9-p1-first-return/BatchCarrySource.lean) and Agent43's [margin-free delayed bridge](../agent43-p1-high-cost-reset-count/LongConeSource.md).

## Reverse block

For a fixed chronological target word y of k bits, write q for the starting clock, c for the starting carry, z for the end carry, and x_i for the selected bits. The exact equation 2 c_(i+1)+y_i=c_i+(q+i)x_i telescopes to

    X=2^k*z+Y=c+q*B+D(B)
    B=sum x_i 2^i, Y=sum y_i 2^i, D(B)=sum i*x_i 2^i.

Conversely, the exact reverse-block theorem proves that a block is legal precisely when
\[
X+\operatorname{corr}(k,B)=(q+k)B+r,\qquad 0\le r<q,
\]
where \(X=2^kz+Y\) and \(B<2^k\). The parity induction establishes every intermediate broad guard; with a zero target word and \(1\le c\le q-3\), it also preserves the strict interior. The identity \(\operatorname{corr}(k,B)=kB-D(B)\), with \(D(B)=\sum_j j2^j\operatorname{bit}_j(B)\), makes the starting carry exactly \(c=X-qB-D(B)\).

The stronger, source-checked fit \(2^{k+1}\le q+k\) gives the two-candidate window
\[
\left\lfloor\frac{X}{q+k}\right\rfloor\le B\le
\left\lfloor\frac{X}{q+k}\right\rfloor+1.
\]
Thus block_reverse.hpp now selects the floor quotient and its successor, rather than the older floor(X/q) and predecessor pair. Agent45's Lean quotient-window and digit-weight proof proves both candidate_window and candidate_remainder_eq; original-source CI [45722244806](https://github.com/FlareZ123/bb6/actions/runs/45722244806) passed with standard axioms. The exhaustive small-range C++ test in ../agent45-p1-delayed-carry/wide_fit_exhaustive.cpp checks 481,220 wide-fit cases (219,724 in the old-fit overlap and 261,496 admitted only by the wider fit), including both strict modes. An independent JavaScript reimplementation of that exact test also passed all 481,220 cases. The implementation has now raised the cap to k<27 after an explicit 64-bit range audit for its input limits n,K<=100,000,000. Every terminal clock satisfies F<=n+K+3<=200,000,003; with k<=26 and z<F, X=(z<<k)+Y<F*2^k<=13,421,773,001,326,592, far below 2^64. Also D(B)<(k-2)2^k+2<=1,610,612,738, and q*B+D(B)<2^64; q and every accepted carry fit signed 32-bit int. The wider fit therefore permits k=20 at F=4,000,000, k=25 at F=68,000,000, and k=26 at F=200,000,000. This is an arithmetic range audit, not a C++ compiler run or performance benchmark. It is an algorithmic acceleration, not a new P1 exclusion; the large prefix-only run has not yet been repeated with the new fit.

The index-weighted digit sum is evaluated by fixed bit masks in block_reverse.hpp. Unlike Agent43's increasing-clock ordinary-map accelerator, this is the fixed-target **reverse** map including delayed bits.

## Folded modular sweep

For the unchanged strict interior 1<=c<=q-3, complement c by q-2-c. At the next clock complement z by q-1-z. The equation 2z=c+qx becomes its complement with bit 1-x. Starting from all terminal endpoints the live sets are symmetric. The canonical coordinate a=min(z,q-1-z) has one folded predecessor min(2a,q-2-2a) if 2a<=q-3, and none otherwise. The center at even clock q is q/2-1. The sorted folded sweep merges one increasing and one decreasing list.

The initial r-step reverse window can be skipped: precisely the starting carries satisfying c+sum (q+j)x_j*2^j=0 mod 2^r survive. Enumerate the residues by iterative union with a cyclic shift, then instantiate them only in the folded interval. Interior preservation is exactly the existing BatchCarry.walk_of_weight argument. [folded_batch.cpp](folded_batch.cpp) chooses a common final clock F<=2L+3 congruent to 11 modulo 2048 when possible, so the 1,3,11 lag coefficients are free. It retains all births in [L,R], with R+4<=F. The independent unquotiented reference agreed on 2916 small cases across six jump lengths.

Exact integer scan results:

| Even indices | F | Folded endpoint visits | Hits |
|---|---:|---:|---|
|7593752..11390626|15185931|335106036|10053630|
|11390628..17085942|22779915|518751869|none|
|17085944..25628916|34170891|814690799|none|
|25628918..38443376|51257355|1287035601|none|
|38443378..57665066|76886027|2060433903|45352466|

Singleton tests at F=2n+3 leave both hits. These intervals contain every even index in the indicated range; prior computations cover smaller n. A subsequent 57.7M–86.5M run was interrupted, so no claim for that range.

## Prefix-only delayed cover

The earlier reverse-forest algorithm retained all terminal endpoints. Instead maintain only Agent45's Covered prefix pairs (B,a) at cost s, represented by the s low bits of 7B, the small multiplication carry r, and a. For each pair and 0<h<=n, use its fixed target bits to rewind **all** broad endpoints at s+n down to s+h. Retain exactly the intermediate carries whose unique h-step reverse prefix ends at a. Recover those selected h bits and append their low multiplication bits. A genuine trace at s+h admitting n further steps has a genuine s-prefix and a continuation through s+n, so this produces a sound cover at s+h. If the candidate list is empty, already no trace at s can extend n steps. No tail image at s+n+h is necessary. Extra candidates at the next stage are harmless and eliminated by the next lookahead.

[prefix_parallel.cpp](prefix_parallel.cpp) uses the reverse-block formula, initial modular residue jump with target Y, and disjoint sets only on the tiny mid-window carry set. The optional checkpoint stores the low-word/carry list rather than huge terminal endpoint sets. The small arithmetic multiplication state and all late margin tests are the same as the earlier reverse_lag.cpp. The margin-free source theorem would also suffice when n+s is within its practical cutoff. No numerical Lean claim.

Build:
    g++ -O3 -std=c++17 folded_batch.cpp -o folded_batch
    g++ -O3 -std=c++17 -fopenmp prefix_parallel.cpp -o prefix_parallel

Run:
    ./folded_batch test
    ./folded_batch 7593752 11390626 20
    OMP_NUM_THREADS=4 ./prefix_parallel 10053630 40214000 1256703

The last returns END 10053630 11310334 (initial two mid-prefix branches, both eliminated at next lookahead; max margin gap 24). Independent old-style reverse-forest and block-forest implementations agreed on that exact safe horizon, width(n+1)=162720. The prefix-only method also reproduced prior safe horizons at n=286,350,1614,2990,3342; these are regressions, not new exclusions.

The larger n=45352466 has first-window width 26604712. Prefix-only stages h=5669058,5669058,11338116 left 2,4,4 prefixes at s=22676233 (no extinction yet). Cap 100000000 is below the practical long-cone cutoff. This is the active unresolved computational exception. Use a fresh checkpoint, choose the specified block sizes successively, and continue rather than counting an END 0 as a proof. The optional checkpoint is an ephemeral local computation state, not a trusted certificate; use fresh runs for reproduction.

## Next useful edge

Formalize the reverse-block arithmetic and prefix-only cover directly against LagCore/LagReverse, then a practical checker that avoids materializing billion-step endpoint sets in Lean. Complete n=45352466 and subsequently extend the range with the faster block algorithm. The remaining infinite-index quantifier is untouched by these finite computations.
