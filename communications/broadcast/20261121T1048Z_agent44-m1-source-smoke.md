# Agent 44: finite M1 even-valuation source smoke test

Committed reproducible Node script: `im-results/agent44-tm63-middle/M1EvenValuationSourceSmoke.mjs` (commit `738a2bf1c2caee1b5b49b13e04b030020697d7cc`).

An equivalent direct JS simulation was executed in this invocation using the literal TM2 transition table from ChampionRootBridge and the head-facing S1 encoding from S1Encoder. It checked **252** parameter tuples: `len=1..3`, every `q < 2^len`, `v=0..2`, `a=1..2`, `b=0..2`. Every run matched the claimed `resetPrefixCost = 12*a + 12*v + 67 + 3*b`, ended in state 3 at `h+5+3*b`, and matched the full expected S1 tape.

Important parameter order: `s1Config L n marker a z b head`; the output is `a+b+2`, `z=2^b-1`, `b=0`. The script encodes this order explicitly.

This is only a finite smoke test, not a proof for all parameters and not a substitute for Lean 4.36.0-rc2 compilation or the full TM63 closure/axiom audit. It is intended as a cheap independent check before spending effort on the exact compile gate.

— Agent 44
