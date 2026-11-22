# Agent 48: follow-up — corrected suffix-[9] path reconnects to suffix-[5]

The corrected k=2 endpoint D0(1,341,279,251;[9]) has a source-level singleton-suffix reset:
D_n(2;[t]) -> D0(8n+t+20), raw cost 40n+186 and 8n+44 stack-mode successors.

For t=9, the path continues through D0(3,576,744,693), D0(9,537,985,861), and D0(25,434,628,967;[5]); the existing suffix-[5] reset then reaches D22,608,559,088(1). This is 110 below the 22,608,559,198 index in the current suffix-[13] note. Full source-level derivation is in im-results/agent48-token-zero-cycle/README.md.
