# Raw139 depth-six F/0 sibling scan

**Status:** computational discovery; the eight candidate side cycles have been added to the Lean residual-witness list and are awaiting CI replay.

The scan reconstructs the raw139 champion-compatible parent after the first six path refinements, leaving F/0, A/1, and B/1 undefined. It enumerates the 23 ordinary F/0 moves other than the champion move `1RA`.

- First-hole scan cap: 1,000,000 transitions per parent.
- For the 15 parents still capped, the deeper run used 5,000,000 transitions and a side-cycle search with entry ≤ 100, period ≤ 200, and boundary radius ≤ 200.
- Of the 8 parents reaching A/1 or B/1 within the initial cap, their 25 first-hole assignments yielded 64 children reaching the remaining hole or an exact lasso, and 136 still capped under the bounded search.
- Of the 15 parents still capped after 5,000,000 transitions, 8 admit the following side-cycle candidates.

| F/0 move | Entry | Period | Direction | Boundary | Translation |
|---|---:|---:|---|---:|---:|
| `0LA` | 93 | 88 | right | -2 | +6 |
| `0RB` | 46 | 9 | right | 3 | +3 |
| `1LB` | 51 | 3 | right | 5 | +1 |
| `0RD` | 39 | 26 | right | 0 | +6 |
| `0LF` | 97 | 96 | right | -2 | +6 |
| `0RF` | 53 | 1 | right | 7 | +1 |
| `1LF` | 52 | 5 | right | 5 | +1 |
| `1RF` | 53 | 1 | right | 7 | +1 |

The corresponding Lean witness entries now added at depth 6 are:

```lean
{ depth := 6, child := ⟨false, false, 0⟩, witness := .side 93 88 true (-2 : Int) },
{ depth := 6, child := ⟨false, true, 1⟩, witness := .side 46 9 true (3 : Int) },
{ depth := 6, child := ⟨true, false, 1⟩, witness := .side 51 3 true (5 : Int) },
{ depth := 6, child := ⟨false, true, 3⟩, witness := .side 39 26 true (0 : Int) },
{ depth := 6, child := ⟨false, false, 5⟩, witness := .side 97 96 true (-2 : Int) },
{ depth := 6, child := ⟨false, true, 5⟩, witness := .side 53 1 true (7 : Int) },
{ depth := 6, child := ⟨true, false, 5⟩, witness := .side 52 5 true (5 : Int) },
{ depth := 6, child := ⟨true, true, 5⟩, witness := .side 53 1 true (7 : Int) }
```

The expected frontier effect is to close eight additional two-hole sibling cylinders, reducing the post-parent frontier from 133 to 125 residual leaves. This is only a forecast until the Lean `championWitnessesOK` and frontier-count theorems pass.

Reproduce with `node scan-f0-two-hole-siblings.mjs` from this directory. The scan is not itself a proof; the Lean `residualWitnessOK` checker is the acceptance criterion.
