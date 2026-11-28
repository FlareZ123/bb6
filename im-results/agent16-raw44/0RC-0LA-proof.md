# Raw44 / B1=0RC / C1=0LA

The complete first-hole partition in [0RC-0LA.json](0RC-0LA.json) has 18,841 nodes, maximal first query time 120, and two residual tables of mass 25 each. They are E/F conjugates. The exact induction gives weighted bound 126, and the complete original-source Lean Cover is accepted in [CI 46107124798](https://github.com/FlareZ123/bb6/actions/runs/46107124798). The residual growth modules passed [M3 run 46106387271](https://github.com/FlareZ123/bb6/actions/runs/46106387271) and [M3Swap run 46106454402](https://github.com/FlareZ123/bb6/actions/runs/46106454402).

Representative M3: 1RB1LE_1RC0RC_0RD0LA_1LD1LB_0RB0LF_1RA---.

Use nearest-first L (excluding head), R (including head), with infinite zero padding. Let T(n) be state E with L=empty and R=110 followed by 2n+1 ones. Blank reaches T(0) in 12 steps.

From T(n), E1,F0,A0,B1,C0,D1,B0,C1,A1 execute exactly 9 moves, producing E with L=11, R=010 followed by 2n ones. In case n=0, R is simply 01 padded. For k>=0 and j>=1, from E with L=0^k11, R=0101^j, execute E0,B1,C0,D1,B0,C1,A1 (7 moves): L becomes 0^(k+1)11 and R becomes 0101^(j-1), all padded. Thus 2n repetitions produce L=0^(2n)11, R=01 padded.

The final reset, with k=2n, executes E0,B1,C0, then D0 for k+4 moves across positions 3,2,...,-k relative to the reset starting head. D1 at -k-1 goes left to B1 at -k-2. Execute B1,C1,A0,B0,C1,A1. The resulting E head is at -k-2, L is blank, R=110 followed by k+3 ones. This is T(n+1). The reset cost is k+14. Therefore T(n)->T(n+1) in 16n+23 positive moves, never querying F1. All hole completions are nonhalting. State swap E/F gives the other residual verbatim.

The complete 18,841-node first-hole tree and both residual growth theorems passed original-source Lean CI in run 46107124798, producing `Cover (WeightedBound 126) parent`. The search generator is untrusted; the emitted tree and residual certificates are kernel-checked. This is a five-hole child only, not a closure of Raw44 itself.
