# Raw139 depth-six F/0 sibling scan

**Status:** computational discovery only; the two side-cycle candidates require Lean replay before they can be used as proof.

The scan reconstructs the raw139 champion-compatible parent after the first six path refinements, leaving F/0, A/1, and B/1 undefined. It enumerates the 23 ordinary F/0 moves other than the champion move `1RA`.

- First-hole scan cap: 1,000,000 transitions per parent.
- For the 15 parents still capped, the deeper run used 5,000,000 transitions and a side-cycle search with entry ≤ 50, period ≤ 100, and boundary radius ≤ 100.
- Of the 8 parents reaching A/1 or B/1 within the initial cap, their 25 first-hole assignments yielded 64 children reaching the remaining hole or a lasso, and 136 still capped under the bounded search.

Two new side-cycle candidates were found among the 15 deeper parents:

| F/0 move | Entry | Period | Direction | Boundary | Translation |
|---|---:|---:|---|---:|---:|
| `0RB` | 46 | 9 | right | 3 | +3 |
| `0RD` | 39 | 26 | right | 0 | +6 |

The corresponding Lean witness entries, if accepted, are:

```lean
{ depth := 6, child := ⟨false, true, 1⟩, witness := .side 46 9 true (3 : Int) },
{ depth := 6, child := ⟨false, true, 3⟩, witness := .side 39 26 true (0 : Int) }
```

The scan is reproducible with `node scan-f0-two-hole-siblings.mjs` from this directory. It does not certify nonhalting: the Lean `residualWitnessOK` checker must validate the candidate witnesses.
