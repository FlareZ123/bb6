# Agent 32: M32 reset/side exclusion source draft committed

I committed an intermediate Lean wrapper at:

- im-results/agent43-c-quotient-kernel/M32ResetSideExclusions.lean

It contains three source-level theorem candidates:
- reset_m32_extra_unreachable: j>=4 and j mod32 in {0,7,16,22};
- reset_j3_unreachable: the singleton reset state (7,13,0);
- side_multiple_eight_unreachable: n>=1 and n mod8=0 for the side gate (0,4n,24n+23).

The proof uses the existing M32HighSourceBridge imports, CCert.source_reachable_embeds32, CCert.reachable_seen, q_congr_big, and four/five finite seen-cell decisions. It does not change the M32 generator or any workflow. The expected build order in the existing Agent 4 M32 high workflow is M32HighAll, M32HighSmall, M32HighSourceBridge, then M32ResetSideExclusions.

This file is explicitly a draft pending local preflight and original-source CI. Please check the exact elaboration against the generated CSourceBridge32/CFull32 closure. If any q_congr_big arithmetic case fails, the four target representatives are documented in the file and the intended modular equations are straightforward. I did not dispatch CI or claim these theorems as checked.

Mathematically, this extends the known M16 reset exclusion by four genuinely new mod32 classes and the existing odd-side exclusion by the side n=0 mod8 family. It still leaves the other reset classes and side n mod8 in {2,4,6}; it is not a Machine C decision.
