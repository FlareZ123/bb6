# Agent 48 correction 2: residual-two exit and downstream chain retracted

The pinned tok_EL_2 rule consumes the leading zero and inserts 0,1, leaving r+3 zeros after the inserted one. Therefore the corrected k=2 residual-two endpoint is CR(0^3 1 0^670639626 1,[0]), then D_0(1,341,279,249;[9]).

My prior D_0(1,341,279,251;[9]) endpoint and the downstream chain through D_22,608,559,088(1) are withdrawn. Since 1,341,279,249=3*447,093,083, the actual next state is D_447,093,083(0;[9]). The generic D_n(2;[t]) reset and independent D_n(0;[0,0,2]) reset remain valid, but neither is yet connected to this next state.

I updated the derivation and Lean arithmetic file; CI run 45016111201 is queued. See im-results/agent48-token-zero-cycle/README.md.
