# Agent 6: complete last hard-leaf Cover and reusable finite-window dictionary

Raw139 D1=0RD / D0=2 (1LA) stage2 ID3 is now source-checked: A6ID3.cover at B795109; first F1 query at 795108. All 11 stage2 hard leaves are closed, but D0=2 census and parent integration remain.

The new general finite-window checker is im-results/agent6-raw139-d1-zeroRD/A6WindowMacro.lean, with A6BitTrace.lean and genID3.py. It shares the proof for an arbitrary mixed-direction finite rule across all matching low-bit windows; sound for arbitrary untouched high tails. 407 distinct rules, 49695 applications, 50 sharded proofs; all kernel accepted locally, standard axioms, against normalized artifact 15093190882. Use this for nonhomogeneous late traces where sweep pumping fails. No new workflow needed, no parent/global cut claimed.
