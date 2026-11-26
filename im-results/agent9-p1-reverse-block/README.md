# Exact reverse-block and prefix-only P1 carry exploration

**Scope and evidence.** This intermediate programme extends the exact-integer P1 critical-index computations beyond the earlier 7,593,750 cutoff, and develops an exact acceleration for both the modular and delayed carry relations. It is not yet a Lean numerical certificate, an all-index reset exclusion, a P1 decision, or a BB(6) bound. The original-source reductions are [BatchCarrySource](../agent9-p1-first-return/BatchCarrySource.lean) and Agent43's [margin-free delayed bridge](../agent43-p1-high-cost-reset-count/LongConeSource.md).


**Exact modular jump (new local preflight).** The converse of `walk_mem_jump` is now proved in JumpResidueSource.lean: for a binary target word of length k, let M=2^k, q=F-k, Y=digits ys, and S=qB+D(B). The residue condition implies (c+S) mod M=Y, because Y<M. Thus z=floor((c+S)/M) satisfies Mz+Y+corr(k,B)=FB+c. The existing `walk_of_eq` derives every intermediate guard from this identity and c<q. Consequently JumpMember is equivalent to existence of a genuine broad Walk, and the lifted residue set is exactly the reverse image of all broad terminal endpoints. No fitted-block condition is needed for this equivalence. The converse and digit bound passed Lean 4.36.0-rc2 locally against exact copied source declarations and proof bodies, with [propext, Quot.sound]; the final original-source integration and axiom audit remain to be run through the existing reverse-live-block target. This improves the certificate interface, not the numeric frontier by itself.

**Bitmap reverse-set implementation.** [prefix_bitmap.cpp](prefix_bitmap.cpp) removes per-block sorting from the unlabelled reverse image by packed membership and in-place deduplication. Its reciprocal quotient proposal is accepted only after exact integer inequalities bF<=X<(b+1)F; otherwise the integer division fallback computes it. The labelled midpoint filter still sorts and merges DSU components. Local compiled regression n=3342, block=417 reached empty cost 13768. For n=45352466 the 5,669,058 / 5,669,058 / 11,338,116 / 22,676,233 schedule reproduced the prior prefixes and reached four at s=45352466. Subsequent 22,676,233-bit blocks gave 8,14,14 prefixes at s=68028699,90704932,113381165. No extinction yet. These are exact-integer finite experiments, not numerical Lean certificates; the optional checkpoint is untrusted. Build with g++ -O3 -march=native -std=c++17 -fopenmp prefix_bitmap.cpp -o prefix_bitmap. The cap 250000000 applies only to this implementation; at n<=100000000, s+n<=K and K<=250000000, F<=n+K+3<=350000003, k<=26, X<F*2^k<2^55 and all signed carry/clock variables and 2*q fit 32-bit int. The margin product A*L<6.0e17 fits uint64_t. Continue with the same prefix schedule; an END n 0 is not an exclusion.

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
Thus block_reverse.hpp now selects the floor quotient and its successor, rather than the older floor(X/q) and predecessor pair. Agent45's Lean quotient-window and digit-weight proof proves both candidate_window and candidate_remainder_eq; original-source CI [45722244806](https://github.com/FlareZ123/bb6/actions/runs/45722244806) passed with standard axioms. The exhaustive small-range C++ test in ../agent45-p1-delayed-carry/wide_fit_exhaustive.cpp checks 481,220 wide-fit cases (219,724 in the old-fit overlap and 261,496 admitted only by the wider fit), including both strict modes. An independent JavaScript reimplementation of that exact test also passed all 481,220 cases. The implementation has now raised the cap to k<27 after an explicit 64-bit range audit for its input limits n,K<=100,000,000. Every terminal clock satisfies F<=n+K+3<=200,000,003; with k<=26 and z<F, X=(z<<k)+Y<F*2^k<=13,421,773,001,326,592, far below 2^64. Also D(B)<(k-2)2^k+2<=1,610,612,738, and q*B+D(B)<2^64; q and every accepted carry fit signed 32-bit int. The wider fit therefore permits k=20 at F=4,000,000, k=25 at F=68,000,000, and k=26 at F=200,000,000. This is an arithmetic range audit, not a C++ compiler run or performance benchmark. A deterministic BigInt stress test, wide_fit_bigint_check.js, exercises 26,000 generated legal blocks across k=1..26 and q up to 200,000,003. It checks unique recovery by the broad two-candidate search, strict-interior acceptance/rejection, z<F, X<2^64, and equality between the C++ fixed-mask digitWeight formula and a direct bit-sum implementation in all 26,000 cases; 4,709 cases lie outside the older fit. It also compares the actual per-bit modular residue update with direct enumeration of every B<2^k in 768 generated cases (k=1..12), covering 104,220 distinct residues. The maximum observed X is 13,042,287,090,381,674. This is reproducible arithmetic evidence, not a C++ compiler run or a proof. It is an algorithmic acceleration, not a new P1 exclusion; the large prefix-only run has not yet been repeated with the new fit.

The initial \(r=\min(22,F-q_0)\) modular jump in prefix_parallel.cpp subtracts the per-bit shifts \((q+j)2^j\) modulo \(2^r\). Their sum is \(qB+\sum_j j2^j\operatorname{bit}_j(B)\), the same digit-weight term used by the exact reverse-block remainder.

**Source proof status (accepted):** ReverseBlockJump.lean proves that every genuine reverse Walk has its starting carry in the modular residue set (walk_mem_jump; CI [45732165534](https://github.com/FlareZ123/bb6/actions/runs/45732165534)). It now also proves walk_mem_prefix_live and trace_prefix_live_candidates (CI [45747514019](https://github.com/FlareZ123/bb6/actions/runs/45747514019)): split an authentic delayed-carry Trace into an earlier fitted block sequence and a final modular suffix; if the suffix endpoint list contains every JumpMember carry, the original prefix carry survives the exact blockFold intersection. All new declarations pass the axiom audit with only propext, Classical.choice, and Quot.sound.

**Concrete residue generator.** [JumpResidueCore.lean](JumpResidueCore.lean) and [JumpResidueSource.lean](JumpResidueSource.lean) formalize the low-bit-first set construction. After j rounds the membership condition is exactly x = (Y - W(q,j,B)) mod M for some B < 2^j, with W(q,j,B)=(q+j)B-corr(j,B)=qB+D_j(B). Extending by a top zero preserves W; extending by a top one adds (q+j)2^j. Deduplication preserves membership. Interval lifting is exact: mem_lift_iff equates membership of the lifted list with JumpMember; liftResidues_cover supplies the previously missing JumpCover premise. The two modules passed local Lean 4.36.0-rc2 preflight against the exact declarations and arithmetic lemma copied from the existing source modules (all printed axioms standard). Full original-source closure is not yet accepted. This is a mathematical set-level model of the C++ seen-table and lifting loops, not formal verification of C++ execution or of the large numerical certificate. For r≤22, unsigned subtraction and masking by 2^r−1 give the same Euclidean residue because 2^r divides 2^32. No P1 index is excluded by the new generator theorem alone.

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

The larger n=45352466 has first-window width 26604712. The bitmap continuation now reaches s=113381165 with 14 candidate prefixes (see current state above). This remains the active unresolved computational exception. Use fresh runs for reproduction; checkpoints are ephemeral, untrusted state.

## Next useful edge

1. Accept the locally preflighted concrete residue generator against the full original-source dependency closure through the existing reverse-live-block target. Then transport actual computed prefix stages to the exact cover and blockFold interfaces.
2. Continue the n=45,352,466 prefix-only computation from the current bitmap experiment; the wider fit has now been exercised on this index. Do not count END n 0 as an exclusion.
3. For any empty live set, connect the exact C++ candidate output to JumpCover and the Lean blockFold specification before claiming a source-certified P1 exclusion.

The remaining infinite-index quantifier is untouched by these finite computations.
