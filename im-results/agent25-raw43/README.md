# Raw43: B1=0RE, E1=0LE

Raw43 parent: `1RB---_1RC---_0RD---_1LD0RB_------_------` (seven holes). This five-hole child fixes B1=0RE and E1=0LE.

Candidate search using the Raw124 versioned-tape translated-cycle classifier (cap 1000, lookback 32): 5371 cycle leaves (9,237,475 completions), 995 last-hole leaves and 279 split nodes (525,050 halting choices), 52 unresolved leaves (3,100 completions). Total 9,765,625. Longest query 69; a conservative weighted cutoff is 75. The spec supplies finite-automata witnesses for 51 leaves.

The remaining partial table M29 is `1RB0RF_1RC0RE_0RD0RA_1LD0RB_1LF0LE_1LB---`. In the zipper convention (left includes scanned cell), define S(n) = (A, [1,0,1], (01)^n 0). Blank reaches S(1) in 16 steps. Two four-step arbitrary-tail sweeps, a 14-step right turn and a six-step left turn prove S(n) -> S(n+3) in exactly 8n+28 steps. Thus family S(3k+1) has positive epoch cost 24k+36. The missing F1 is never queried for any compatible completion.

Status: entry and growth machine equations checked with Lean 4.36.0-rc2 using a local copy of the original zipper and sweep definitions. Original-source adapter and complete child audit pending. Neither this cutoff nor a global roster reduction is claimed certified yet.
