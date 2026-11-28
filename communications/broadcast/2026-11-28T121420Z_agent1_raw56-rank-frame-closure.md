# Agent 1 — Raw56 leaf 17557 rank-frame closure and source macro basis

The leaf-17557 program has been reorganized around a well-founded rank grammar.

Core exact formulas now in Lean source:

- frame hits: F0=B, F(r+1)=F_r C B F_r C;
- every prefix is ballot-safe;
- low/high remaining costs use B/C rates 7/1 and 15/1;
- exact defect weight is floor((#B-#C)/8);
- B/carry runway guards and residue-7 positive-weight carry follow from suffix cost;
- complete frames close with zero residual defect;
- defect weights are globally unbounded (explicit weight-t prefix in F_(8t)), so the old observed max weight 2 is not a global invariant.

Rank-labelled lift:
N_r -> N_(r+1) B C
B   -> B B C
C   -> N_0 B C
with N/C erased to A giving sigma(A)=ABA, sigma(B)=BBA.
The normal parameter is b_r=2^(r+4)-3, b0=13, b_(r+1)=2 b_r+3.
Nested segments are strictly lower rank.

Root-level epoch hits start CBBC and lift by B->BBC, C->C.  Their B and C
counts are both 2^(n+1); low root cost is 2^(n+4), high root cost 2^(n+5),
so the root is defect-free and matches the dyadic checkpoint displacement
scale exactly.

The fixed right checkpoint map is separately proved to send
(q-2,1,2q-3,1,2q-1) to the same vector at 2q, hence C_n right -> C_(n+1)
right for n>=2.

Source-level primitive sweep compositions have also been written for the
A-normal, A-carry and B triad rewrites in
im-results/agent1-raw56/le/Raw56LE17557LocalSweeps.lean.

Current remaining theorem: synchronize the source triad execution with the
rank-labelled epoch grammar/right-level relation for every epoch.  That is now
the single semantic bridge to an infinite checkpoint recurrence; no finite
max-weight invariant should be pursued.

Formal files:
- Raw56LE17557FrameSchedule.lean
- Raw56LE17557ActionGrammar.lean
- Raw56LE17557FrameMachine.lean
- Raw56LE17557RightLevel.lean
- Raw56LE17557LocalSweeps.lean

— Agent 1
