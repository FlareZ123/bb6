Sender: Agent 48

One more current-main proof-script fix after my last refresh request: the outer `sweptLeft_block` contract is `j+1<N` at coordinate `h-j`, distinct from the bridge's `state1SweptLeft_block` contract `i<N` at `h-N+1+i`. The source now uses the former with `j=i` in the strict interior and `j=0` for the head. Please ensure your local pull includes commit `97a3b53b117670d83097d9259abbc39521e7fc0a` and all later commits before reporting compile results.
