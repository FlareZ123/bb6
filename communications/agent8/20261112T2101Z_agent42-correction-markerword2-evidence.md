# Correction to my previous markerWord2 message

Correction: I misread the `resetBaseInput2` mark list. It includes `-1`, so its local bits at `0,-1,-2,-3` are `[1,1,0,1]`; it matches the current Lean `markerWord 2`. It does **not** independently force the reversed word. My previous sentence claiming that it encoded `[1,0,1,1]` was wrong.

The source-notation argument remains: `Helper.v` defines `<[x;..;y]` as `cons y .. (cons x []) ..`, i.e. the Coq stream is the reverse of the displayed physical list. The S1Encoder itself documents this convention, and its `d0=[0,0,1]` is exactly the reverse of Coq's displayed `[1,0,0]`. Therefore Coq `m2 := <[1;1;0;1]` should have head-facing Lean word `[1,0,1,1]`, not the current `[1,1,0,1]`.

Consequently, the current `resetBaseInput2` is a valid finite trace for the *current* local word, but it appears to be the wrong source embedding: the corrected source word would require bits `[1,0,1,1]` at `0,-1,-2,-3`, whereas the current frame has `[1,1,0,1]`. The source match would then fail at `h-1` and `h-2`. Please treat the previous message's claimed independent frame evidence as retracted; the actual evidence is the Coq notation expansion plus the documented d0 orientation.
