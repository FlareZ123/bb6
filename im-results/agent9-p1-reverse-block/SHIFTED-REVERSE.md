# Shifted divisor and greedy high-bit reverse blocks

For a block of k fixed target bits, let q be the lower clock, F=q+k, M=2^k, X=Mz+Y. Write D(B)=sum i*2^i*bit_i(B) and C(B)=sum (k-i)*2^i*bit_i(B). The existing ReverseBlock source equivalence says a legal reverse word B<M has X+C(B)=F*B+a with 0<=a<q. All intermediate guards follow from the same equality.

## Wider two-candidate fit

C(B)-B is nonnegative and at most sum (k-i-1)*2^i = M-k-1. Let G=F-1. For k>=1 and M<=G, X+(C(B)-B)=G*B+a, with both a and C(B)-B less than G. Hence floor(X/G)<=B<=floor(X/G)+1. Test these two exact candidates only. This improves the former sufficient fit 2^(k+1)<=F to 2^k<=F-1.

For u=B+1<M, t=v2(u), the increment D(B+1)-D(B)=t*2^t-sum_{i<t} i*2^i=2^(t+1)-2. Thus adjacent weights qB+D(B) differ by q+2*lowbit(u)-2. The second candidate requires no second digit-weight computation.

## Greedy extension

For a high bit at position j, H=2^j, its weight is (q+j)*H. For any lower word L<H and carry a<q, qL+D(L)+a < (q+j)*H (for j=0, L=0). Thus that high bit is forced by the comparison X >= (q+j)*H; subtract the weight if set and reduce the problem to j bits. Both directions are exact, including gaps. Strip any number of high bits, then apply the shifted two-candidate fit to the remaining r bits if 2^r<=q+r-1.

## Implementation and evidence

- ShiftedReverseBlock.lean: exact source equivalence; initial CI 45950012982 accepted the three shifted-fit lemmas, but failed later elaboration; corrected proof commit 34f2eec46e15772ce844d586480ec71ac29398bf **accepted** by CI [45950357692](https://github.com/FlareZ123/bb6/actions/runs/45950357692). All eight declared theorems use only standard Lean axioms, no sorryAx/native_decide.
- shifted_reverse.hpp: scalar and AVX512 implementation; compact_prefix.cpp selects mode P1_FIT=0..5 (0 is unchanged default).
- shifted_reverse_test.js: independent exact arithmetic test executed 2026-11-27 06:03Z: 1,297,686 exhaustive small cases, of which 647,790 outside former fit; 50,000 large stress cases and 50,000 adjacent identities. Old two-candidate search outside its proven fit missed 1,914 of the legal stress examples. Largest X=2300203870779464640. CI 45950357692 additionally passed 12,979,208 small, 2,400,000 large and 2,400,000 SIMD cases, with identical n3342 child lists and END 3342 13768 across modes 0..5. Mode 1 was best on this runner: 17,151.5 vs 13,458.5 million clock-queries/s at F=650M, 17,336.9 vs 13,584.6 at F=1B. These are isolated throughput figures, not total scan speedups.
- Existing unresolved n=45352466 run 45935332194 ended at the 900,000,000 budget, not extinction. Last checkpoint s=884372737, 23 canonical children, artifact 15172862750. No new critical-index exclusion follows merely from this optimization.

For implementation purposes F<INT_MAX, k<=32, X<2^63. Mode selection remains opt-in generally; the existing packed-prefix-compact workflow now selects mode 1 for its actual continuation, after accepted tests. A 1.1B continuation from artifact run 45935332194 was dispatched 06:14Z (no result yet). A failed initial proof audit is not a certificate; do not classify the critical index on this basis.
