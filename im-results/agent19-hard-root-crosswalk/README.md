# Hard-root crosswalk to the accepted canonical 77

Status: computational routing aid, not a new kernel certificate or global upper bound. Pinned manifest revision `492de8b66f8c905b97472e1092244bf3f90e07f8`, blob `3a131a18edd89b56bf7f8cf9cd6229961652829f`. Canonical root representatives are selected using the exact least-fresh-state address rule of Agent47's CanonicalFrontier, followed by the 18 Combined106 exclusions and raw114 exclusion (CanonicalRaw114Accepted, CI 45554648116). This reproduces 124 → 96 → 78 → 77. No standalone parent certificate is counted as consumed unless present in that accepted roster.

All 15 completed roots below start at A on blank tape with 1RB, already in first-use canonical form: no reflection, relabeling, or initial blank delay is needed. Every root visits all eleven ordinary rows before the sole halt row. This is a finite prefix observation, not a nonhalting proof. The JSON distinguishes completed halt tokens from null partial holes and records every compatible root-fixing permutation, including aliases eliminated by canonicalization.

| Root | Raw residual ID | Manifest index | Sole halt slot | Last ordinary row first queried at | Max blank-delay surcharge | Retained permutation witnesses |
|---|---:|---:|---|---:|---:|---:|
| champion | 139 | 102 | B1 | 213 | 0 | 2 |
| C | 10 | 6 | F0 | 22 | 0 | 6 |
| P1 | 8 | 4 | F0 | 37 | 0 | 6 |
| Sheep | 8 | 4 | F0 | 100 | 0 | 6 |
| D0 | 10 | 6 | F1 | 36 | 0 | 6 |
| D1 | 9 | 5 | A1 | 94 | 0 | 6 |
| D2 | 10 | 6 | F1 | 92 | 1 | 6 |
| D3 | 13 | 8 | F1 | 23 | 0 | 6 |
| A6 | 139 | 102 | F1 | 110 | 2 | 2 |
| r1 | 10 | 6 | D1 | 52 | 2 | 6 |
| r2 | 9 | 5 | F0 | 35 | 0 | 6 |
| r3 | 9 | 5 | F0 | 38 | 0 | 6 |
| r4 | 23 | 13 | F1 | 15 | 0 | 2 |
| r5 | 8 | 4 | F0 | 22 | 0 | 6 |
| r6 | 23 | 13 | E0 | 62 | 0 | 2 |

Each root matches exactly one retained canonical parent, but several permutations may witness compatibility. Raw IDs are stable manifest identifiers, not positions in the accepted 77. The surcharge column is computed on the completed original table, not on all completions of its containing parent.

## Exact downstream obligations

For a one-halt completed table m, erase its sole halt row to obtain a 25-completion leaf. The 24 ordinary replacements have no halt row and hence are nonhalting; only m requires a decision or time bound. The existing lastHole_of_good theorem in agent48-counted-inc0/ChampionLastHoleCover.lean and weighted_never in agent13-weighted-first-one/WeightedTNF.lean express this. At attained champion score B, the missing condition for m is that every HaltsAfter m k satisfies k+1+maxDelay ≤ B; a nonhalting proof also suffices. This is an exact condition by the definition of WeightedBound, with the surcharge calculated from zeroNext terminal paths. The computed finite graph and paths here are not independently kernel-checked.

* C, D0, D2 share raw10. C's source reduction and exact 25-completion lemma are in agent4-machine-c-global-path; C requires resolving the joint low/high reachability gate or bounding its halt time at B. D0 and D2 have distinct seeds I9 and I15. D2 has a nonzero delay surcharge. D1 goes to raw9 (I39); D3 to raw13 (I5). Their source bridge is agent3-d-boundary-portfolio/DRootTransfer.lean.
* P1 and Sheep share raw8. P1's sparse-gate equivalence is in agent19-p1-source-bridge; Sheep's even-return problem is in agent16-sheep-even-return. Neither arithmetic root is resolved here.
* Champion and A6 share raw139 but diverge immediately at D1: champion 0LE, A6 0LC. The latter is not in the active champion F1 sibling search. A6 already has a source-accepted literal_never proof (CI 41529738637) and twentyFive_cover in agent8-coverage-contract/F287HaltFreedom.lean. Its 25-completion leaf can be consumed at any weighted score via WeightedNonhaltLeafAdapter.forgetHaltRows_nonhaltCertificate. The exact first-hole schedule after A0 is recorded in JSON. A leaf is not a proof of its 8-hole D1=0LC ancestor; all other siblings must remain.
* r1–r6 are the six original-source accepted Cryptids roots from agent42-cryptids-current-main (CI 45178351479), already closed in the physical depth-four frontier. Their first-hole schedules have an existing integration in agent8-cryptids-tnf-paths. Their presence in raw8,9,10,23 is a routing fact, not a new decision or a proof that those parents are closed.

## Reproduction

Run `node im-results/agent19-hard-root-crosswalk/crosswalk.cjs` against the pinned manifest and compare with crosswalk.json. The computation checks the roster counts, canonical first-use order, all 24 A/B-fixing permutations and unique retained raw ID. It uses the exact literal root tables, not historical numerical machine identifiers. Sources: results/2026-11-24-champion-exact-attainment.md; agent11-c-line/README.md; agent19-p1-source-bridge/README.md; agent16-sheep-even-return/README.md; agent3-portfolio-raw-conjugacy/README.md; agent4-coverage-smoke/CryptidsF287.lean; agent42-cryptids-current-main/README.md.

No new machine decisions, exhaustive parent covers, or roster-count reductions are claimed.
