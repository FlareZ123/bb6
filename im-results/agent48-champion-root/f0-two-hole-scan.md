# Raw139 depth-six F/0 sibling scan

**Status:** ten candidate side cycles have been added to the Lean residual-witness list; the updated frontier audit is pending.

The scan reconstructs the raw139 champion-compatible parent after the first six path refinements, leaving F/0, A/1, and B/1 undefined. It enumerates the 23 ordinary F/0 moves other than the champion move `1RA`.

- First-hole scan cap: 1,000,000 transitions per parent.
- The 15 parents still capped were deepened to 5,000,000 transitions. A side-cycle search with entry ≤ 100, period ≤ 200, and boundary radius ≤ 200 found eight witnesses.
- A second search on the seven remaining parents used entry ≤ 200, period ≤ 400, and boundary radius ≤ 400; it found one additional witness (`0LD`).
- An optimized incremental search on the six remaining parents used entry ≤ 300, period ≤ 600, and boundary radius ≤ 600; it found one additional witness (`0RE`).
- Of the eight parents reaching A/1 or B/1 within the initial cap, their 25 first-hole assignments yielded 64 children reaching the remaining hole or an exact lasso, and 136 still capped under the bounded search.

The ten side-cycle candidates are:

| F/0 move | Entry | Period | Direction | Boundary | Translation |
|---|---:|---:|---|---:|---:|
| `0LA` | 93 | 88 | right | -2 | +6 |
| `0RB` | 46 | 9 | right | 3 | +3 |
| `1LB` | 51 | 3 | right | 5 | +1 |
| `0LD` | 148 | 23 | right | 10 | +3 |
| `0RD` | 39 | 26 | right | 0 | +6 |
| `0RE` | 265 | 41 | right | 11 | +3 |
| `0LF` | 97 | 96 | right | -2 | +6 |
| `0RF` | 53 | 1 | right | 7 | +1 |
| `1LF` | 52 | 5 | right | 5 | +1 |
| `1RF` | 53 | 1 | right | 7 | +1 |

The corresponding depth-six Lean witness entries are in `ChampionResidualFrontier.lean`. A separate Python replay independently checked each entry/period, state return, positive translation, one-sided head condition, and tape-shift condition. Formal acceptance still depends on the Lean `championWitnessesOK` theorem.

Expected frontier effect: the parent certificate closes 23 final A/1 children, and these ten side cycles close ten F/0 siblings, taking the raw139 frontier from 156 to 123 residual leaves. The 123 open residual cylinders include 13 unresolved F/0 siblings plus earlier-depth branches. The 109-roster refinement therefore has 200 obligations (77 other canonical representatives + 123 raw139 residuals).

The additional closed mass is 6,825 raw completions: 575 from the parent certificate's 23 children and 6,250 from ten two-hole side-cycle siblings. This is a local refinement, not a closure of raw139 as a whole.

Reproduce the first stage with `node scan-f0-two-hole-siblings.mjs`, the next search with `node search-f0-remaining-deeper.mjs`, and the optimized final search with `node search-f0-remaining-optimized.mjs`.
