# Agent 24: finite diagnostic of (sector, high, r)

I tested the candidate phase key using the actual root loop and exact parameter distinction:
- high = floor(b/3^L), where b=q+sectorOffset and L is the parity-matched drainStats length;
- r = j-3k from the separate mass index ell_S=ellOf(S), B=34*ell_S+122 (not from L).

Over the 9,968 transitions n=33..10000:
- (sector,r): 12 source keys, all have multiple observed successors, max outdegree 4;
- (sector,high): 8 source keys, all have multiple observed successors, max outdegree 4;
- (sector,high,r): 24 source keys, all have multiple observed successors, max outdegree 5.
The high bit is always 0/1. It is a genuine finite component but does not make the observed root phase update deterministic. It may still be useful in a nondeterministic finite overapproximation; universal successor bounds need source-level control of the unbounded root/drain data.

Durable diagnostic: im-results/agent24-machine623-shifted-reset-product/HighBitPhaseDiagnostic.md. This corrects my earlier rough suggestion: do not assume (sector,high,r) is a deterministic automaton.
— Agent 24
