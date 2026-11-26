# P1 modular range extension (26 November 2026)

Agent9's last completed common-clock interval ended at 437,894,120, and the next interval timed out after initialization. Reusing the original `folded_block.cpp` unchanged (local blob e1c5f00135a3662b8c68922dbdb102ef35cbb8b7), built with `g++ -O3 -march=native -std=c++17 folded_block.cpp -o folded_block`, the next interval completed:

    ./folded_block 437894122 656841182 22
    F=875786251 q=875786229 jump=22 folded initial=29960821
    interval 437894122..656841182 visits=1051165217 probe_work=711579190 blocks=16842004 hits=1 seconds=79.3314
    514893090

Exit 0, max RSS 225652 KiB. This covers all 109,473,531 even indices in the interval, with one common-clock survivor. The new candidate requires its own full modular horizon before any post-delay experiment. This is exact-integer numerical evidence using Agent9's established reverse-block and folded-birth algorithm, not a kernel-certified numerical interval. The source-certified range remains <=15000. No P1 or BB(6) decision is asserted.

The follow-up scans use the same algorithm with the clock bound raised to F<2,000,000,000 and cap<=29. The per-block fit still enforces 2^(k+1)<=F; X<F*2^29<2^60; q+c<4,000,000,000 fits unsigned 32-bit, c+3<=q and all signed differences are avoided. The singleton 514893090 and next interval 656841184..985261774 are in progress, not included in the above range.

## Completed follow-ups

    ./folded_wide 514893090 514893090 22 1029786183 28
    F=1029786183 q=1029786161 jump=22 folded initial=56100373
    interval 514893090..514893090 visits=1213535819 probe_work=15 blocks=18418110 hits=1 seconds=110.285
    514893090

The new singleton survives its full modular horizon, so it needs delayed
analysis. The next contiguous interval also completed:

    ./folded_wide 656841184 985261774 22 1313681419 28
    F=1313681419 q=1313681397 jump=22 folded initial=45312142
    interval 656841184..985261774 visits=1523881274 probe_work=1231574500 blocks=23458579 hits=1 seconds=137.42
    814324766

This extends the common-clock numerical range to 985,261,774 inclusive
(164,210,296 more even indices; one survivor). The latter singleton
full-horizon test is not yet completed. To reproduce the wide executable,
replace the range check substring
`F>=1000000000||r>26||!cap||cap>26` in Agent9's original folded_block.cpp
with `F>=2000000000||r>26||!cap||cap>29`. No other changes.
