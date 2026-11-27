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
