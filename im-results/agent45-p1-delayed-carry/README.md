# Post-n delayed-bit carry certificates

Status: exact computational proof method; universal arithmetic inequalities and generic fitted-block Covered integration are kernel-checked. A source-connected numerical certificate of the large scans remains future work. The six finite extinction horizons and margin goals were already identified by Agents28/43. This is a new compressed representation, not a claim to discover these exclusions or close the entire P1 frontier.

## Current formal methods (25 November 2026)

The original delayed model is now formalized in LagCore.lean and LagChecker.lean; the original-source [margin-free transfer](../agent43-p1-high-cost-reset-count/LongConeSource.md) excludes the authentic critical reset from empty Covered n s [] for even n≥8000, s≥1 and n+s≤practicalCut n+1. This supersedes the need for the separate margin inequalities in that range. The margin method remains useful under its original hypotheses.

**Exact reverse blocks.** ReverseBlock.lean proves a k-step identity for fixed target bits and decreasing modulus F−i: put X=2^k z+Y, with Y the chronological target digits encoded as a binary integer, and R(B)=Σ_{i=1}^k i b_i 2^(k−i). The endpoint equation is X+R(B)=FB+r, B<2^k, r<F−k. These conditions imply every intermediate strict range guard. When 2^(k+1)≤F, the only candidate wrap words are floor(X/F) and floor(X/F)+1; at most one works. The exact equivalence fast_iff_walk is kernel-checked. ReverseBlockCompose.lean establishes composition for arbitrary fitted partitions, ReverseBlockLagTrace.lean proves the delayed Trace prefix coverage, and ReverseBlockSource.lean proves live_block against Agent9's unchanged BatchCarry.lean (blob e25870aa80076f1325f4a43ffeedb5b35c326e87). All compiled locally, standard axioms only. The generic delayed Covered integration is now source-checked in ReverseLagBlocks.lean (details below); a concrete finite certificate generator/checker for the large survivors remains separate.

**Fitted-block delayed Covered bridge (25 November).** `ReverseLagBlocks.lean` imports the unchanged `LagCore`, `LagChecker` and `LagCert` sources and proves `extend_to_walk`, `blockLookahead_sound`, `covered_next_block` and `cert_next_block`. For any partition `bs` of the chronological delayed target word satisfying `Fitted (n+s+3) bs`, membership in the exact `blockFold` image is a necessary condition for a genuine n-step `Extend`. Filtering `advance` by this Boolean therefore preserves `Covered`, and the existing full `Cert` margin invariant composes unchanged. The proof deliberately needs only the sound direction: extra block-fold candidates are harmless false positives, while an empty image is decisive. Pinned original-source CI [45718702944](https://github.com/FlareZ123/bb6/actions/runs/45718702944), source commit `33f6c2c360259ab8dec98dfdf5b630016b52a41b`, passed Lean 4.36.0-rc2 and the standard-axiom audit (no `sorryAx`, no `native_decide`). This is a reusable proof-method improvement, not a new numerical P1 exclusion or a completed large-index certificate.

The C++ regression reverse_block.cpp is exact unsigned arithmetic, with 454787 exhaustive and 1000000 random scalar/block comparisons. A synthetic zero-target sweep from F=4156615 to 2078310 used 204434101 scalar endpoint visits in 0.928s versus 40504647 visits in 0.418s with hybrid threshold 262144, same final five carries. This is a speed test, not a new critical-index exclusion. Agent9's [larger finite screening](../agent9-p1-first-return/README.md) already reaches 7593750 computationally.

**All-period obstruction.** [The delayed-carry aperiodicity theorem](../../results/2026-11-25-p1-delayed-carry-aperiodicity-agent45.md) rules out every fixed eventually periodic binary word as an infinite Trace witness. It gives the exact nonzero signed numerator and finite divisibility constraint for every period, including nonprimitive periods, and is kernel-checked against unchanged LagCore.lean. It does not rule out aperiodic witnesses or decide P1.

## The representation

Use Agent50's exact Micro coordinates v=(d-1)/2, w=(b+12)/2 and T=7P, P=2^n. A micro history of positive length m has a word x_0,...,x_(m-1) with x_0=1, where one is a new odd inverse step and zero is a continuation. Set
    B_m=sum_{i<m} x_i 2^i,
    E_m=sum_{i<m} x_i (n+i+3) 2^i.
The exact identities are
    2^m v+(E_m-1)=7P B_m,
    2^m w+(E'_m-1)=7P B'_m,
where B'_m=2^m-B_m, and E'_m uses x'_0=1 and x'_i=1-x_i for i>0. These follow directly by induction from Micro.one/zero (multiply by 2^(m+1)), or from the Agent50 word identities with complementary words. In particular E_m and E'_m are positive and both offsets E-1 are at most A B, with A=n+K+2 for m<=K.

The first identity implies E_m-1 = 7P B_m (mod 2^m). Its low-bit matching can be computed without ever storing the original large carry v. Let y_i be bit i of 7P B_m: y_i=0 for i<n, otherwise bit i-n of 7 B_m. Since n>=1, this target bit depends only on earlier choices. The small weighted carry a_1=(n+2)/2 (even n) updates by
    a_(i+1) = (a_i + x_i(n+i+3) - y_i)/2,
requiring an even nonnegative numerator. Indeed 2^i a_i = E_i-1-(7P B_i mod 2^i). Prefix congruence at i+1 is exactly parity of the numerator. Nonnegativity is automatic for a valid congruence: E_i-1>=0 and the target residue is less than 2^i. Inductively a_i<=n+i+2, so the carry set at layer i fits in a bitset of O(n+i) bits. A carry-set transition is
    S' = compress_even((S OR (S << (n+i+3))) >> y_i).
The set contains each nonnegative carry satisfying the transition (and no others). Empty layers are absorbing.

## Lookahead and block pruning

For each low prefix of length s, store its word B_s and its small carry a_s. To test whether it has an extension to total cost n+s, all target bits through n+s-1 are already fixed by B_s. Thus an ordinary carry-set DP starting from {a_s} at s over the next n positions decides this question exactly. Keep only low prefixes passing the lookahead test. A valid word of length n+s projects to a valid word of every earlier length: weights above the truncated prefix vanish modulo the corresponding power of two, and multiplication by 7P respects that congruence. Consequently all possible longer histories must extend a previously retained low prefix.

To reduce tests, extend a retained prefix by a whole block of h low bits, requiring integrality at each low step, then test n-step lookahead only at the new block boundary. This is complete: no valid low prefix can be skipped. The blocks used here have length 32, except n=30 uses 4; first boundary s=1, last s=K-n. If no candidate survives the final test, there is no congruent word of length K, hence no Micro history of length >=K (truncate the genuine history). This is stronger than just a finite-depth check of legal inverses.

## Margin certificate without storing the large states

For 0<m<=n, put D=2^m. Since D divides 7P, each positive weighted offset F=E-1 is a positive multiple of D. From D v+F=7P B, F<=A B, A<=P one gets 6P B<=D v and D<=A B; therefore 6P<=A v. Same for w.

For m=n+s, s>0, put D=2^s, and let r=(7B_s mod D), which is odd and in [1,D-1]. The two target residues are P*r and P*(D-r), because B'_m=2^m-B_m. In either identity P D v+F=7P B the residue P*r is <=F. If v<=L then
    6P B<=P D L,  6B<=D L,  P*r<=F<=A B,
so 6P*r<=A D L. Hence
    6P min(r,D-r) > A D L
implies v>L and w>L. LagMargin.lean proves the early and late inequalities in ordinary Lean (no native axioms).

For a little-endian s-bit representation of r, let g=min(s,1+length of its most-significant constant-bit run). Since r is odd, min(r,D-r)>=2^(s-g): if the leading run is zeros, the first one witnesses the bound, and if ones, the first zero witnesses the corresponding complement bound; the all-ones case has D-r=1. Appending h high bits grows g by at most h. Thus at a block starting from a retained prefix with gap g, it suffices to check
    6*2^(n-g-h) > A L
for every layer in that block (require g+h<=n). This does not enumerate full-P states or their margins. For the root m=0 we separately have v=1,d=3 and w=7P-n-2.

Taking L=2(n+3K+10)+6 gives the two non-root conditions in Agent43's GateConditions directly: v>L implies d!=5; w>L implies b/4>=n+3K+10. The root satisfies them by its explicit formula. Together with extinction and Agent43's cone_no_reach_of_conditions, this is a mathematical route to original-source critical reset exclusion. The original margin arithmetic proof remains useful; the newer source-accepted margin-free transfer is described above.

## Exact finite experiment

Build: g++ -std=c++17 -O3 -march=native lagblock.cpp -o lagblock
Run without arguments for the six known exceptional (n,K) cases, or pass n K block. Negative exit results are failures to certify, never positive results. Elapsed wall times are informational only; all decisions are exact integer bit operations.

| n | K | block | peak retained prefixes | peak candidates | maximal certified gap bound | lookahead tests | DP steps |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 30 | 82 | 4 | 4 | 16 | 11 | 101 | 1208 |
| 286 | 1442 | 32 | 6 | 124 | 43 | 1625 | 62216 |
| 350 | 586 | 32 | 2 | 48 | 36 | 201 | 7876 |
| 1614 | 5824 | 32 | 4 | 140 | 42 | 5393 | 582156 |
| 2990 | 6154 | 32 | 4 | 180 | 39 | 3521 | 673170 |
| 3342 | 13730 | 32 | 8 | 312 | 42 | 25245 | 5185002 |

All six experiments reached the previously known extinction horizon with the margin bound. Locally the three large scans took roughly 0.21, 0.26 and 4.05 seconds respectively (not a benchmark promise). Only a handful of low-prefix words survive at block boundaries. The retained-prefix representation suggests small formal checkpoints: a verified checker can reject every rejected extension by an ordinary small carry-set DP and compose block coverage. Source certificates already pending for these indices may be completed via the older full-P approach first; avoid duplication. The general purpose of this method is to extend beyond these examples and support stronger delayed-bit constraints.
