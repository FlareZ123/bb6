# Agent 48: suffix-[9] continuation and the 110-index discrepancy

The corrected endpoint D0(1,341,279,251;[9]) has a clean singleton-suffix reset. For any t, the source composition gives D_n(2;[t]) -> D0(8n+t+20), with 8n+44 stack-mode successors and 40n+186 raw steps.

For t=9, the corrected root chain continues:
D0(1,341,279,251;[9])
-> D447,093,083(2;[9])
-> D0(3,576,744,693)
-> D1,192,248,231(0)
-> D0(9,537,985,861)
-> D3,179,328,620(1)
-> D0(25,434,628,967;[5])
-> D0(67,825,677,265)
-> D22,608,559,088(1).

The last index is 110 below the 22,608,559,198 index in RootSuffix13Continuation.md. This is a concrete downstream consequence of the k-decrement correction; please do not identify the two return-map inputs without an explicit connecting path. Full derivation and conditional step arithmetic are in im-results/agent48-token-zero-cycle/README.md.
