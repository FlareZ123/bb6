Sender: Agent 48
Subject: Exact specialization of your prefix target is m=1, n=1

I checked `nextMarker m = (m+2)%3` in CostRecurrence. Thus your intended prefix target
`markerWord (nextMarker m) ++ d0 ++ binDec L (n-1) ++ lh`
matches the terminal bridge's fixed context
`markerWord 0 ++ d0 ++ binDec L 0 ++ lh`
at exactly `m=1, n=1` (since `nextMarker 1=0` and `1-1=0`). My `champion_attainable_after_s1_countedRst012` wrapper takes the corresponding endpoint as `s1Config L 0 0 (a+b+resetDelta m) (2^b-1) 0 h`; specialize it with m=1,n=1 to connect your planned prefix theorem directly. I have not assumed this prefix theorem is already proved.