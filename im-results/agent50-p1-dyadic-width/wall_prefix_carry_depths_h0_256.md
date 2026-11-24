# Exploratory carry-depth atlas for the two restart progressions (h = 0…256)

**Status:** reproducible computation, not a theorem about all (h). This scan is preserved because it exposes large and highly irregular prefix-survival transients; it warns against assuming a small uniform carry cutoff.

For each family parameter (h\in[0,256]), run the exact carry-set recurrence
[
C_1=\{(n+2)/2\},\qquad
C_{j+1}=\left\{c/2:c\in C_j,\ 2\mid c\right\}
\cup
\left\{(c+n+3+j)/2:c\in C_j,\ 2\mid c+n+3+j\right\}.
]
The first empty layer (K) is the first prefix depth at which no Boolean subset with (x_0=1) can satisfy the source-wall congruence modulo (2^K). All 514 cases (257 per family) reached an empty layer before the 10,000-step cap; there were no cap hits.

## Largest first-empty depths

| Family I: (n=5362+595056h) | Empty depth (K) | Largest carry-set size | Layer of largest set |
|---:|---:|---:|---:|
| 142 | 5350 | 1304 | 1640 |
| 10 | 2012 | 672 | 856 |
| 74 | 1790 | 792 | 718 |
| 121 | 1206 | 608 | 260 |
| 166 | 422 | 360 | 264 |
| 177 | 404 | 184 | 300 |
| 129 | 334 | 148 | 236 |
| 145 | 320 | 248 | 156 |
| 62 | 286 | 164 | 196 |
| 13 | 278 | 232 | 156 |
| 78 | 246 | 120 | 174 |
| 17 | 198 | 112 | 62 |
| 133 | 150 | 56 | 46 |
| 29 | 134 | 40 | 94 |
| 225 | 124 | 48 | 30 |
| 213 | 110 | 48 | 24 |
| 229 | 94 | 48 | 62 |
| 33 | 92 | 40 | 54 |
| 34 | 86 | 40 | 46 |
| 174 | 86 | 60 | 72 |

| Family II: (n=9538+703248h) | Empty depth (K) | Largest carry-set size | Layer of largest set |
|---:|---:|---:|---:|
| 86 | 4750 | 744 | 2638 |
| 57 | 1484 | 472 | 1076 |
| 150 | 838 | 340 | 268 |
| 149 | 612 | 484 | 148 |
| 153 | 528 | 224 | 176 |
| 90 | 366 | 136 | 72 |
| 54 | 278 | 128 | 190 |
| 85 | 208 | 72 | 150 |
| 81 | 206 | 120 | 86 |
| 193 | 176 | 68 | 108 |
| 122 | 172 | 64 | 44 |
| 6 | 160 | 68 | 84 |
| 77 | 140 | 52 | 24 |
| 174 | 134 | 72 | 88 |
| 245 | 134 | 72 | 44 |
| 190 | 128 | 104 | 86 |
| 197 | 100 | 40 | 78 |
| 13 | 94 | 48 | 38 |
| 105 | 94 | 56 | 46 |
| 249 | 92 | 52 | 44 |

The worst cases (h=142) in family I and (h=86) in family II survive 5,349 and 4,749 prefix layers respectively. Thus a proposed argument that all (h) are eliminated by a small fixed prefix depth is not credible without a new structural invariant. The four Lean-checked cylinders in [`wall_prefix_carry_cylinders.md`](wall_prefix_carry_cylinders.md) remain exact infinite subfamily results, but they do not capture these long-transient branches.

## Reproduction

The scan used JavaScript `Number` arithmetic only on integers below (2^{53}), and `Set` to deduplicate carry states:

\`\`\`js
function firstEmpty(n, maxSteps = 10000) {
  let states = new Set([(n + 2) / 2]);
  for (let j = 1; j < Math.min(n, maxSteps); j++) {
    const C = n + 3 + j, next = new Set();
    for (const c of states) {
      if ((c & 1) === 0) {
        next.add(c / 2);
        if ((C & 1) === 0) next.add((c + C) / 2);
      } else if ((C & 1) === 1) {
        next.add((c + C) / 2);
      }
    }
    states = next;
    if (states.size === 0) return j + 1;
  }
  return null;
}
\`\`\`

This is an exploratory census over (h\le256), not a universal proof. The next mathematical step is to explain the long transient structure (especially the (h=142) and (h=86) cases), rather than simply extending the same finite scan.


The full driver that loops over both families and all 257 values of (h), records maximum state-set sizes, and prints the top 20 records is [`wall_prefix_carry_depths_scan.js`](wall_prefix_carry_depths_scan.js).


Since the maximal observed depths satisfy (5350<5362\le n) in family I and (4750<9538\le n) in family II, and the terminal-cost cutoff gives (m\ge n), this census computationally excludes a source-wall state for **every** (0\le h\le256) in either family, conditional on the source identity. This finite-range conclusion is still only as strong as the Set-based computation; unlike the four cylinders in the companion Lean file, the full (h\le256) batch has not been kernel-certified.
