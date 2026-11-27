# Folded reverse-block birth localization

The P1 modular screen has a unique folded reverse parent whenever one exists, and the only canonical folded class with no strict parent is the maximal class. This eliminates all forward probes of candidate central births during a fitted reverse sweep.

For a clock F and canonical carry z, define S(k) to mean that z admits a strict folded suffix of length k. It is downward closed. If a fitted k-step reverse query fails, binary search the maximal surviving length l<k. The unique folded ancestor at F-l is necessarily the maximal carry floor((F-l-2)/2). If that clock is even, this is precisely the central birth for n=F-l-4. Conversely a surviving central birth strictly above the lower boundary of the block forces a failure there, because the birth has no parent. A successful query cannot contain any maximal folded ancestor strictly inside its traversed block. The final lower boundary is explicitly checked; the initial modular jump is chosen so its lower endpoint is at or above the largest requested birth clock.

BirthLocate.lean proves the structural statements against Agent9's FoldedWalk/BatchCarry interface; all six declarations passed local Lean 4.36.0-rc2 with unchanged relevant dependency definitions/proof bodies and only standard axioms. BirthLocateSource.lean proves strictParent_iff, boundary_spec, testSuffix_iff, locate_spec, locate_center, mem_lostClocks and lostClocks_live against the existing fitted source reverse interface. Local preflight used the exact signature of the already-proved source_fast_iff as a temporary dependency stub; full-source manual CI was dispatched separately. No temporary stub was committed. These are general algorithmic theorems, not yet a numerical certificate of the runs below.

## Exact integer experiment

Build `g++ -O3 -march=native -std=c++17 birthloc.cpp -o birthloc`. Run `./birthloc test`: 20,610 complete hit-list comparisons with the independent scalar unquotiented reference passed, varying jump length and block size. The 4-billion clock cap is safe: clocks and strict carries fit uint32_t; all products in fitted queries (k<=29, F<4e9) fit uint64_t. The reference is used only for small tests. The reciprocal quotient proposal is checked by exact inequalities and falls back to exact division.

New contiguous even-index range, immediately following the earlier scan through 985,261,774:

    ./birthloc 985261776 1477892660 22 1970523531 29
    F=1970523531 q=1970523509 jump=22 folded initial=99733035
    interval 985261776..1477892660 visits=2283183500 locate_probes=257 failed_blocks=52 blocks=34083508 hits=1 seconds=86.6715
    1187661906

Full modular horizon of the one hit:

    ./birthloc 1187661906 1187661906 22 2375323815 29
    F=2375323815 q=2375323793 jump=22 folded initial=134440156
    interval 1187661906..1187661906 visits=2794959174 locate_probes=210 failed_blocks=43 blocks=40953859 hits=0 seconds=136.702

Every even index in the new interval passes the modular exclusion screen, with no remaining candidate. There are 246,315,443 even indices in the inclusive interval. The prior unresolved candidates (notably n=45,352,466 and n=814,324,766) are not thereby resolved. This is new exact-integer evidence, not an original-source Lean numerical certificate or a P1/BB(6) solution.

The difference from the old fitted forward-probe sweep is particularly large in the sparse phase: only 257 in-block suffix tests across 34,083,508 blocks, rather than probing each eligible birth separately. Dense endpoint visits still dominate. A future dense word-plane implementation can emit the failed endpoints by scanning the gaps between consecutive legal endpoint intervals instead of evaluating every endpoint individually.

## Second contiguous extension, 2026-11-27

    ./birthloc-wide 1477892662 2216838992 22 2955785327 29
    visits=3445960743 locate_probes=288 failed_blocks=59 blocks=50961816 hits=2 seconds=181.188
    1947933202 2201221694

Both common-clock hits were then eliminated by the new dense-gap hybrid:

    ./dense_birthloc 1947933202 1947933202 3895866407 22 29 24
    F=3895866407 q=3895866385 jump=22 folded initial=227418865
    dense blocks=1 clocks=18 q=3895866367 live=149563019 sec=3.96249
    interval 1947933202..1947933202 visits=4621524243 locate_probes=277 failed_blocks=57 sparse_blocks=67170109 hits=0 seconds=285.926

    ./dense_birthloc 2201221694 2201221694 3999999999 22 29 24
    F=3999999999 q=3999999977 jump=22 folded initial=324829101
    dense blocks=1 clocks=18 q=3999999959 live=153136990 sec=4.30272
    interval 2201221694..2201221694 visits=4738947643 locate_probes=295 failed_blocks=60 sparse_blocks=62026837 hits=0 seconds=279.281

The second singleton's horizon is shorter than 2n+3, hence extinction there suffices. Total new coverage is 615,788,609 even indices in [985261776,2216838992]. No new candidate survives. These are reproducible exact-integer experiments, not kernel-certified numerical exclusions. The earlier exceptions n=45352466 and n=814324766 remain open computationally as of this checkpoint.

Build dense_birthloc.cpp with g++ -O3 -march=native -std=c++17; without arguments its 808 exact dense/pointwise comparisons and sweep regressions passed. The strict source endpoints for a fixed selected word W=qB+D(B), M=2^k, form the interval [floor(W/M)+1, floor((W+q-3)/M)], clipped to canonical bounds. The intervals are disjoint and ordered (W(B+1)-W(B)>=q), and the dense pass transposes interval bits into carry planes, localizing births only in gaps. StrictPlaneGaps.lean locally proves interval arithmetic and the generic ordered-gap complement with standard axioms. Source binding for the dense implementation is still needed. BirthCover.lean provides a one-sided arbitrary-length live/birth cover: every input endpoint may be covered by a witnessed lower ancestor or by a witnessed maximal ancestor, making exact intermediate image equality unnecessary. Its six structural theorems passed local Lean on exact dependency excerpts; no full-source CI for this module yet.
