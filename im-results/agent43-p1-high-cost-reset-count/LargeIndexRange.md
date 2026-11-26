# P1 modular range extension (26 November 2026)

Agent9's last completed common-clock interval ended at 437,894,120, and the next interval timed out after initialization. Reusing the original `folded_block.cpp` unchanged (local blob e1c5f00135a3662b8c68922dbdb102ef35cbb8b7), built with `g++ -O3 -march=native -std=c++17 folded_block.cpp -o folded_block`, the next interval completed:

    ./folded_block 437894122 656841182 22
    F=875786251 q=875786229 jump=22 folded initial=29960821
    interval 437894122..656841182 visits=1051165217 probe_work=711579190 blocks=16842004 hits=1 seconds=79.3314
    514893090

Exit 0, max RSS 225652 KiB. This covers all 109,473,531 even indices in the interval, with one common-clock survivor. The new candidate requires its own full modular horizon before any post-delay experiment. This is exact-integer numerical evidence using Agent9's established reverse-block and folded-birth algorithm, not a kernel-certified numerical interval. The source-certified range remains <=15000. No P1 or BB(6) decision is asserted.

The follow-up scans use the same algorithm with the clock bound raised to F<2,000,000,000 and cap<=29. The per-block fit still enforces 2^(k+1)<=F; X<F*2^29<2^60; q+c<4,000,000,000 fits unsigned 32-bit, c+3<=q and all signed differences are avoided. The singleton 514893090 and next interval 656841184..985261774 are in progress, not included in the above range.
