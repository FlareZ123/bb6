# #623 root phase-search record

This note consolidates finite phase-selector tests on the 20,000-transition source-faithful blank-root replay. It is an intermediate research aid, not a proof.

## Base data

The canonical replay and its metrics are in RootGapScaleScan.js and README.md. Agent 32's independent 20,000-step source-matching replay is in im-results/agent32-623-gap-slack/scan.mjs.

For root states at indices 9..19,999, the four observed sectors have minima:

| Sector | Minimum slack |
|---|---:|
| right-odd | 65 |
| left-even | 124 |
| right-even | 310 |
| left-odd | 452 |

The 19,991 transitions from index 8 to index 19,999 use only eight sector edges, listed in README.md. This is an observed itinerary graph only.

## Phase selectors tested and found insufficient

Agent 32 tested coordinate residues, scalar drain statistics, and short sector histories:

- Grouping by (sector, a mod q, d mod q): at q=3, all 36 classes exhibit both outgoing edges; at q=9, all 324 do; at q=27, 2,653 of 2,912 remain ambiguous; at q=81, 2,600 of 13,919 remain ambiguous.
- Adding abs(a-d) mod 3 to the q=3 key still leaves every class ambiguous.
- Conditioning on exact drainB iteration count: 3,808 of 8,782 classes are ambiguous.
- Conditioning on exact evalA loop count: 4,481 of 7,391 classes are ambiguous.
- Conditioning on exact number of recursive r=1 steps: 3,639 of 5,121 classes are ambiguous. Parity/mod-3 of these counts also fails.
- Previous k sector labels, for k=1..4, leave every class ambiguous.

I additionally retained the exact ternary remainder path from evalA calls:

- Current sector plus the last 1..6 complete evalA call paths leaves respectively 58/67, 333/483, 1,007/1,927, 1,907/5,282, 2,426/10,102, and 2,052/14,507 classes ambiguous.
- Current sector plus the last 32 raw ternary remainder symbols leaves 695 ambiguous classes out of 18,950.
- The entire transition remainder word identifies each transition uniquely, which is merely the full transition trace and not a useful compact phase.

Finally, current sector plus simple 3-adic valuations also fails to select the next sector:

| Valuation | Classes | Ambiguous |
|---|---:|---:|
| v3(abs(a-d)) | 33 | 30 |
| v3(g) | 33 | 30 |
| v3(g-9m) | 35 | 29 |
| v3(4g+9m) | 31 | 28 |

Here g=a-4d when a>=d and g=d-4a otherwise, and m=min(a,d).

These are finite partitions of the same root trace; they do not prove that no larger modulus or richer statistic works. They do show that a small coordinate residue, scalar drain count, short sector suffix, short terminal quotient-path suffix, or one simple valuation is insufficient.

## Counterexamples against state-local slack invariants

The observed 65-slack minimum is not a universal one-step certificate.

- D(2,10) satisfies the six-slack implication to newAffineCone but maps to D(10,9), outside the cone.
- D(2,69) satisfies 65-slack but maps to D(70,10), losing slack (while remaining in the cone).
- D(18,88) has h=70,m=18 and slack66, but maps exactly to D(70,65), outside newAffineCone.

Therefore neither the 6-slack nor the 65-slack predicate is a generic forward invariant. The root's 20k orbit has additional history/phase structure that these state-local inequalities do not capture.

## Research implication

Do not repeat the small residue, scalar drain-count, short sector-history, or short quotient-suffix tests without a materially new feature. The evidence points toward a compressed cocycle retaining more of the full ternary quotient/remainder path, or a root-specific arithmetic relation that couples several transitions. Any proposed invariant must distinguish the authentic blank-root itinerary from synthetic states such as D(18,88), not merely restate the observed slack lower bound.


## Residue-dependent slack table is not closed

I computed the minimum slack observed in each of the 36 (sector, a mod 3, d mod 3) classes on the 20k root trace and used those minima as class-specific thresholds. This contains the entire scanned root prefix by construction, but it is not forward-invariant even on small states.

Counterexample: D(2,73) is right-odd with residues (2,1), slack 69, exceeding the root-trace minimum 65 for that class. Its exact next state is D(74,10), which is left-even with residues (2,1) and slack 61, far below the root-trace minimum 696,153 for that target class. By contrast, the authentic root state D(314,385) has the same source sector/residue class (right-odd, (2,1)) and slack 65, but maps to D(74,950), whose target class is right-even (2,2) with slack 871.

Thus even sector plus mod-3 residues plus a class-specific slack threshold does not encode enough of the root history. The quotient/drain path or a stronger arithmetic invariant is still needed.
