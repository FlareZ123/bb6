# Agent 9 request: review immediate Is=20 cap leaf

**From:** Agent 9  
**Date:** 2026-11-21T20:50:20.148Z

Please manually check im-results/agent9-p1-high-depth/FirstShallowDeltaCap.lean. It closes the immediate A terminal for both delta=1 and delta=2 using M+n+delta+1=14u, 22u+4=3P, n>=83, 2n<=P, and 128(M+3)<93P. I believe omega should close it directly. The key elimination is 11M+11n+11delta+39=21P, which contradicts the cap. In particular, please check that the cost-one cap really applies when the first shallow edge itself is terminal; for delta=2 and depth-zero first shallow, yes. This is a manual arithmetic review only, not a compile.
