# Resumable prefix-only delayed-carry search (2026-11-26)

The v1 trial at n=45352466, h=34014336, K=181409864 ended with 22 surviving prefixes at s=170071681. No extinction was established. The earlier practical 4n cutoff is insufficient for this schedule.

V2 adds an AVX-512 fitted reverse block (scalar fallback); quotient estimates are corrected using exact integer inequalities, with division fallback. Local comparison: 904000 endpoints; synthetic 100M-clock 20-block trials, initial 1M and 5M endpoints, about 1.82x speedup versus scalar. This is not an end-to-end speedup claim.

A bounded forward probe can give exact terminal sets cheaply; exceeding its work cap triggers the full reverse search, never an extinction claim. For a prefix product residue R=(7B) mod 2^s, let ell=min(s,1+length of top homogeneous bit run). Then min(R,2^s-R)>=2^(s-ell): when ell<s the top ell bits include both digits; at ell=s oddness gives the bound 1. Thus the stronger block test 6*2^(n-h-ell)>(n+K+2)*marginSize(n,K) implies the existing MarginOK test, via resMin_extend. Reflection exchanges R and 2^s-R for odd B, preserving the margin; a formal source adapter remains to be checked.

The ancestry transcript records parent index and midpoint carry, reconstructs the unique selected prefix and its product on load, and checks margins for the requested horizon. It is **not** a completeness certificate: omitted children are not detected by replay. The fresh search is necessary for that.

Build and run:
    g++ -O3 -march=native -std=c++17 -fopenmp plane_prefix_v2.cpp -o plane_prefix_v2
    ./plane_prefix_v2
    ./plane_prefix_v2 3342 10000 417 100000 small.txt
    ./plane_prefix_v2 3342 14000 417 100000 small.txt
    OMP_NUM_THREADS=3 ./plane_prefix_v2 45352466 362819728 36281920 10000000 45m.txt

Tests passed 243 selected-word recoveries, 16 probe/reverse and live-set comparisons, and 4095 exact residue-loss checks. Small-index restart reproduced extinction cost 13768. The large run is partial: stages 1,36281921,72563841 have respectively 5,20,18 surviving prefixes. No BB(6) upper bound or numerical Lean certificate is claimed.
