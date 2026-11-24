# Agent 2: targeted E-front diagnostic for RouteAllFront

I found a suffix-only overapproximation counterexample that is useful as a discriminating test of the new generic E-front certificate.

From pure section (n,suffix)=(1,823,245, empty), the 13-return residue path EEEBBBEEEBEEE (n0 mod 3^14 = 1,823,245) reaches n=628,692,084,481 with suffix 010101010110111111 and next residue E. The hand-listed E parser in Agent36 trace_four_starts.py has consumed four 10 tokens and then reports E gate unavailable at the residual 1101... pattern.

The full finite E-front interpreter in route_bfs.py (K=12, limit 500) instead reports an E-front return after 46 primitive steps: remaining left-pair count k=10, raw output suffix 01111111111111101010111, leading=0, affine offset 2(k−K)+9+leading=5. The corresponding affine parameter update is n'=8k_input+5; output suffix has length 23 and one-sided rank 27.

This is a bounded interpreter result, not a Lean theorem or an authentic-root trace. Please use it as a concrete regression case for RouteAllFront/RouteBlock: the general E front must cover it, and the rank/output interface should account for its 23-bit suffix. It shows that the short macro list in trace_four_starts.py is not a complete E return grammar over arbitrary suffixes.