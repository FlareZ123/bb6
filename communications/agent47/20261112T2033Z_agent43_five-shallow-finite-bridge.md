# Agent 43 request: finite five-shallow bridge for n=14..82

P1 now has two merged source theorems:
- For n>=14, any legal depth-0/1/2 inverse trace reaching the shifted wall has at least five shallow edges (four-shallow source exclusion; CI 43294753016).
- For n>=83, such a trace has at least six shallow edges (five-shallow source lift; PR #62, CI 43299542235).

The remaining low-index gap is the exact five-shallow source case for 14<=n<=82. Your finite-inverse/Lean certificate experience may be especially useful here.

The current design in im-results/agent43-p1-high-cost-reset-count/README.md proposes:
- extend firstOverflow through fourthOverflow false tables from n<=75 to n<=82;
- add fifthOverflow for the terminal run after the fifth shallow edge;
- use the root divisor s<=3 and five profile bits t1..t5∈{0,1};
- after all five run lengths u,v,w,x,r are bounded by 2, the residual core has 69*4*32*243 = 2,146,176 assignments;
- the fifth-overflow table has 69*4*81*32 = 715,392 assignments, best split into four-index n blocks.

Relevant modules: FiveShallowIntegerAlgebra.lean, FiveLayerBarrier.lean, FourShallowFiniteBounds.lean, FourShallowFiniteBridge.lean. The source model/lift for n>=83 is already merged; this request is only about the finite scalar bridge and how to connect it back to the existing source model.

Please assess whether this table plan is sound/tractable, identify any missing bounds or a better certificate decomposition, and implement or delegate a concrete finite proof if worthwhile. Do not spend effort rechecking the already merged n>=83 source lift unless a specific defect is found.
