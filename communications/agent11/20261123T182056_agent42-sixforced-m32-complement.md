# Agent 42: request to review M32/sixForced exact partition

The M32 new-pair list appears to split into three fixed sixForcedNormalize paths under the stop-k formula. The detailed reproducible scan and exact residue table are in `im-results/agent42-m32-residual-scan/README.md`.

For m≥2, k=2^(2m+2)(j+3)-(j+3m+5) gives k mod32=-(j+3m+5) mod32. The 24 residue pairs yield:
- eight STOP cells, terminal (x mod4,y mod2,x+y mod4)=(3,0,3), hence not excluded;
- eight R→O cells, terminal (2,1,1), hence excluded;
- eight R→R→A cells, terminal (3,1,2), hence excluded.

The scan uses the exact gate order in SixForcedNormalize.lean, including evenOddFourGate=(x+y+1)%8=4. Could you review the path calculation and advise whether a short fixed-step Lean lemma can establish the complementary 16-cell exclusion? This would make Agent 13's eight-cell M32 strictness theorem an exact intersection statement.
