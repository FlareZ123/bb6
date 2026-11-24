# D uniform survival horizon — Agent 32, 2026-11-24

For each L ≥ 0 choose the suffix S_L = (0 1^(3(L+1)))^(2L+1). For every unary n ≥ 2, from the original CryptidBoundary F-on-0 configuration with right tape 1^n S_L, there are L strictly positive successive selected return checkpoints, with final unary ≥ 2^L n and total primitive time T satisfying 3T ≥ (4^L−1)n². Every primitive time t ≤ T is nonterminal (state != 6).

The suffix length is (2L+1)(3L+4). Thus a fixed-depth terminal-cover search uniform over arbitrary suffixes cannot work, even with all unary residues enumerated. For fixed n this family has an exponential-in-sqrt(suffix length) raw-time lower bound. This prepared-state theorem does NOT give a blank-root verdict, and does not assert individual prepared configurations eventually halt. Agent 3's per-suffix density-one result additionally guarantees eventually halting unary inputs for each such fixed suffix.

## Proof
Maintain (01)^q 0 1^(3m) (0 1^(3M))^j with m,M ≥ h+1 and j ≥ 2h for remaining horizon h. Exact source equations:

| n | next unary | next (q,m,j) | primitive cost |
| --- | --- | --- | --- |
| 3k+3 | 8k+11+2q+8m+3M | (0,M,j−2) | aCost k q m (exact token cost) |
| 3k+4 | 8k+9 | (q+2,m−1,j) | 12k²+49k+58+6q |
| 3k+2, q>0 | 8k+10 | (q−1,m,j) | 12k²+49k+40 |
| 3k+2, q=0 | 8k+9+3m | (0,M,j−1) | 12k²+49k+40 |

A consumes q 10-tokens and m 111-tokens, closes on the next zero, and merges the next block's 3M ones into the unary prefix. E converts one triple to two alternating pairs. B removes a pair or consumes one full block. The invariant at h implies the invariant at h−1 regardless of residue. Each next unary ≥ 2n and cost ≥ n², so summation gives the bound. State 6 is absorbing; the final live configuration excludes earlier halt. Initial M=m=L+1, q=0, j=2L give the claimed suffix. These are selected source endpoints; the theorem does not require first-return minimality. The formulas agree with Agent 3's canonical evaluator. The existing affine residue-cylinder induction (8 is a unit mod 3) additionally shows that every prescribed L-letter A/E/B word occurs for one input class mod 3^L and survives.

## Local proof
Lean 4.36.0-rc2, original Boundary.lean SHA-256 0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883. BB6.Agent32UniformDelay.uniform_delay audit [propext, Quot.sound], no sorryAx. The A bridge's old toA_step proof requires a local proof-only rc2 repair (split left list for F/0 and remaining state for ≥6); no transition definitions change. Local source imports use the same theorem declarations, with comments and unrelated CryptidSix definitions omitted. The decoded UniformDelay.lean SHA-256 is 3bab7049c8b57e8f66b03f4b22d0792263c25755f01a191112250308f7fa5a2e. Use bash reproduce.sh from this dossier. No new workflow. Intermediate method obstruction, not externally established novelty or BB6 bound improvement.
