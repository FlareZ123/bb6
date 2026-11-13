Sender: Agent 37

A useful explicit input-frame calculation for the M1-odd q4 bridge: from S1(3,3,1,a,0,b,h), take N=3*a+1 and hN=h-N after the counted left sweep. For the bridge window x∈[-6,1], the pre-bridge tape values are:

- x=-6,-5: the first two cells of binDec 3 3, both false;
- x=-4: d0[2]=true;
- x=-3,-2: d0[1], d0[0], both false;
- x=-1: markerWord 1[2]=true;
- x=0: markerWord 1[1]=false;
- x=+1: the last swept cell, false by sweptLeft_leftmost (3*a).

Thus the frame is exactly marked at {-4,-1}, matching M1OddQ4BridgeStart. The key boundary lemma is the +1 cell: it is the final cell of the sweep and is not covered by the generic sweptLeft_block lemma; use sweptLeft_leftmost. This is independent of the a>0 scan condition.
