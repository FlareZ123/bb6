# Hard-root → canonical residual crosswalk (77-representative frontier)

Requested by Critic's 2026-11-25 hard-root-to-frontier message. This is a coordination map, not a closure theorem. The source manifest canonical-124.json (blob 3a131a18edd89b56bf7f8cf9cd6229961652829f) was filtered by rooted state introduction to 96 addresses, then the 18 accepted cuts and Raw114 were removed, obtaining 77. Each complete machine below was compared against every surviving partial table using all 120 root-fixing state permutations and both directions. HALT in a complete table is an actual undefined transition, whereas manifest null represents a free slot. All rows have a literal identity-permutation/nonreflected match and exactly one surviving raw parent ID (there can be multiple permutations for unused labels).

| Named complete root | Literal transition table | Raw residual | Canonical manifest index | Exact parent |
|---|---|---:|---:|---|
| Champion | `1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE` | 139 | 102 | `1RB---_1RC---_1LD---_------_------_------` |
| D0 (I9) | `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` | 10 | 6 | `1RB---_1LC---_------_------_------_------` |
| D1 (I39) | `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` | 9 | 5 | `1RB---_0RC---_------_------_------_------` |
| D2 (I15) | `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---` | 10 | 6 | `1RB---_1LC---_------_------_------_------` |
| D3 (I5) | `1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---` | 13 | 8 | `1RB---_1RC---_1LA---_------_------_------` |
| Sheep | `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` | 8 | 4 | `1RB---_0LC---_------_------_------_------` |

Literal table sources: results/2026-11-24-champion-exact-attainment.md, im-results/agent3-portfolio-raw-conjugacy/README.md, im-results/agent16-sheep-even-return/README.md. The 77-roster proof is CanonicalRaw114Accepted.lean (accepted CI 45554648116). This computational crosswalk does not change any theorem or accepted count.

**Operational implication:** D-family and Sheep work belongs inside extremely large early-divergence cylinders (9 or 10 remaining transition slots). A whole-machine result supplies a single completion's leaf certificate, not a whole parent Cover. Future global refinements should first produce a sound partition down to the exact full/partial machine containing each cryptid, with a sibling certificate plan; otherwise even a decisive cryptid theorem cannot by itself shrink the canonical roster. The champion raw139 refinement is already pursuing this strategy. Avoid assigning duplicated root-specific work to different parent owners.
