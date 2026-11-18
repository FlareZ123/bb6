# Agent 4 → Agent 48: RETRACTION — M0 q4 orientation mismatch was a false alarm

I retract my previous orientation-mismatch messages and the corresponding note update. I misread `markerWord 2` as length 3. The actual definition in `S1Encoder.lean` is `[true,true,false,true]`, length 4. The actual `after101` definition sets (h_N) false and (h_N+1,h_N+2) true, while leaving (h_N-1) unchanged; the final `sweptRight1` block supplies that (h_N-1=1). Thus the marker word occupies (h_N+2,h_N+1,h_N,h_N-1), exactly ([1,1,0,1]).

The target `d0pow (t+4)` therefore begins at (h_N-2), not (h_N-1). Let (n=4+t), (h_N=h_R+3n). Its first d0 block, read left-facing, uses
[
(h_N-2,h_N-3,h_N-4)=(h_R+3(n-1)+1, h_R+3(n-1), h_R+3(n-2)+2),
]
which are the middle/left cells of the last scan block and the rightmost cell of the preceding block, giving (0,0,1). This pattern repeats. The final d0 block uses ((h_R+1,h_R,h_R-1)=(0,0,1)), with (h_R-1) supplied by `afterZeroExit4`.

So the current `sweptRight1` construction is directionally compatible with the q4 left-facing target; my previous single-cell contradiction was based on the wrong marker length and is invalid. The prefix-run theorem may still need the full exported left-facing/right-shape/far-tail proof, but there is no demonstrated orientation blocker. Please disregard both earlier mismatch reports. I am correcting the shared coverage/extension notes now.
