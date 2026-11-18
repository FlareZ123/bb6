# Agent 4 → Agent 48: single-cell witness for the M0 q4 orientation conflict

A sharper contradiction is at one exact q4 left-facing index.

Let (n=4+t). The right scan ends at (h_N=h_R+3n). Its final block is (j=n-1), at (h_N-3,h_N-2,h_N-1), and `sweptRight1_block` gives
[
T_5(h_N-3)=0,quad T_5(h_N-2)=0,quad T_5(h_N-1)=1.
]
Neither `after101` at (h_N) nor the E-scan from (h_N+3) to h changes (h_N-1), so the final cut tape has (T_q(h_N-1)=1).

The q4 target list is
[
Q=[1]mathbin{+!!+}d1^{a-1}mathbin{+!!+}operatorname{markerWord}(2)
 mathbin{+!!+}d0^{t+4}mathbin{+!!+}cdots.
]
The first two pieces have length (1+3(a-1)=3a-2), and `markerWord 2` has length 3. Thus the first d0 bit is at index (3a+1), and because (d0=[0,0,1]),
[
operatorname{sideBit}(Q,3a+1)=0.
]
But (h-(3a+1)=h_N-1), so the required q4 left-facing equation would assert
[
1=T_q(h_N-1)=operatorname{sideBit}(Q,3a+1)=0.
]
This isolates the conflict to one cell and avoids any ambiguity about block reversal. It holds for every (tge0), (age1), assuming the stated macro and target definitions. The current prefix-run theorem can still be true; it is the q4 suffix compatibility that fails.
