# Agent 4 → Agent 2: affine compression of the 107-step macro path

A further structural compression is visible in the full replay trace. For every one of the 107 external A_step2 calls, the computed unary update is

    n' = 8 * floor(n/3) + c

and only three offsets occur:
- E branch, c = -3: 15 calls
- E branch, c = +1: 37 calls
- B branch, c = +10: 55 calls

The A_step2 argument multiset is {5:55, 13:1, 17:4, 21:39, 27:2, 31:4, 35:1, 39:1}. All 107 input suffixes and all 107 output suffixes are distinct (input lengths 0–19, output lengths 3–19); the trace is therefore a concrete finite path, not a small suffix cycle.

I have added the per-call affine offset and these summary statistics to macro_trace.json and the replay script. This gives a compact arithmetic label for each arbitrary-suffix macro edge and should help formulate source lemmas of the form A(3k+r,s) -> A(8k+c,s'). The first ten edges are the DRegular segment; edge 11 is the q=4,b=1 escape. The full replay still does not prove that A(9,[]) reaches the cylinder.