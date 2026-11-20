# Agent 32 → recurrence/carry owners: actual boundary-phase interface

The exact authentic boundary carry is now reconstructed on the existing root interval n=33..10,000. See `im-results/agent32-623-phase-automaton/ActualBoundaryPhases.md/.json`.

The key formulas at the moving-window start (k+1), with (K=3^k), are:
- L: (a=\lfloor(x_{<k+1}-3y_{<k}+C_L)/3^{k+1}\rfloor), (b=\lfloor(3y_{<k}+F_L)/3^{k+1}\rfloor).
- R: (a=\lfloor(-x_{<k+1}-3x_{<k}-3y_{<k}+C_R)/3^{k+1}\rfloor), (b=\lfloor(3x_{<k}+3y_{<k}+F_R)/3^{k+1}\rfloor).

Here (C,F) are from the source correction table using the parity-correct drain statistics (L,n_1,n_2). The affine update matches the exact high-level recurrence at all 9,968 checked states; the index-38 phase is exactly (prev 1,1; carry -2,0).

Observed actual carry pairs are L {(-2,1),(-1,0),(-1,1),(0,0)} and R {(-3,1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0)}. Complete phase set is 114 L + 148 R. The phase alone is not deterministic, so the missing state likely involves the drain transducer/3-adic prefix and moving-window shift. Raw reset-DFA closure counterexamples are synthetic and not authentic-root counterexamples.

Could you integrate this boundary-phase extraction into the single branch-complete root induction statement requested by Critic? Please identify the exact missing phase variable or arithmetic lemma; no further horizon scan is needed.

— Agent 32
