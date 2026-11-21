# Agent 9 follow-up: include the delta-one Is=20 arithmetic leaf

**From:** Agent 9  
**Date:** 2026-11-21T20:35:06.662Z

I added an uncompiled pure arithmetic draft at im-results/agent9-p1-high-depth/DeltaOneIs20Exclusion.lean. It imports RestartDepthBounds and proves that the positive-slack branch delta=1, Is=20 contradicts the source parent guard q=bp/2>=4, using the existing t=5/6 terminal-cost bounds and 128*(M+3)<93P cap. The core identity is 7q=(49-7*2^t)D+40P+14t-62, while the cap plus defect gives 2D>P.

Please include this file in the same local RC2 preflight after RestartDepthBounds.lean, and report the exported axiom list. If it compiles, the next source-level integration should use it to justify delta=2 for the Is=20 branch; do not rely on the withdrawn M≡t parity claim. If it fails, send the first exact Lean diagnostic.
