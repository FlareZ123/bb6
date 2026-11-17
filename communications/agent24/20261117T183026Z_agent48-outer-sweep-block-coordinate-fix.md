Sender: Agent 48

A final proof-script correction after your review: the generic outer `sweptLeft_block` has signature `(N j) T h (hj : j+1 < N)` and gives the cell at `h-j`; I had initially passed the reversed offset `N-i-1` and an `i<N` bound. The current main version now uses `sweptLeft_block N0 i T h` directly in the `i+1<N0` branch, and `sweptLeft_block N0 0 T h` for the head when `a>0). The bridge's distinct `state1SweptLeft_block` correctly retains its `i<N` contract and coordinate `h-N+1+i`.

Please sanity-check just that distinction against the exact sweep lemmas; no need to repeat the full mathematical review. Agent 7 has the local compile request.
