# 623: 94-state paired carry closure and root-window experiment

**Status:** intermediate computational result; not yet a formal source-seed theorem or an all-time BB(6) proof.

## 1. Finite transducer closure

Extend the existing 66-state paired carry set from `im-results/agent49-parity623/PostResetCarryPairInvariant.lean` by two seeds:

- `(px,py; L=(-2,1); R=(-1,0)) = (0,2;-2,1;-1,0)`
- `(px,py; L=(-1,0); R=(0,0)) = (0,1;-1,0;0,0)`

Here a paired state is
`(px,py,leftA,leftB,rightA,rightB)`, and an input symbol is a digit pair `(x,y)∈{0,1,2}²`. The simultaneous carry update is

```
leftA'  = floor((x - py + leftA)/3)
leftB'  = floor((py + leftB)/3)
rightA' = floor((-x - px - py + rightA)/3)
rightB' = floor((px + py + rightB)/3)
(px',py') = (x,y).
```

Breadth-first closure of the 66 existing states plus these two seeds under all nine input pairs has **exactly 94 states**. The closure is exact: every one of its 94 states transitions back into the set for every input pair. The left carry projections lie in `{(-1,0),(0,0),(-2,1),(-1,1)}`; the right carry projections lie in `{(-1,0),(-2,0),(-2,1),(-3,1),(0,0)}`.

The full 94-state set is specified compactly by the 13 carry projections below; each row gives the allowed previous digit pairs `(px,py)`.

| Left carry | Right carry | Previous pairs | Count |
|---|---|---|---:|
| (-1,0) | (-1,0) | all except px=2 | 6 |
| (-1,0) | (-2,0) | all 9 | 9 |
| (-1,0) | (-2,1) | all 9 | 9 |
| (-1,0) | (-3,1) | all 9 | 9 |
| (0,0) | (-1,0) | all 9 | 9 |
| (0,0) | (-2,0) | all 9 | 9 |
| (0,0) | (-2,1) | all 9 | 9 |
| (0,0) | (-3,1) | px=1 or 2, any py | 6 |
| (-2,1) | (-1,0) | px=0, any py | 3 |
| (-1,0) | (0,0) | (px,py)=(0,1) | 1 |
| (-1,1) | (-2,0) | px=1 or 2, any py | 6 |
| (-1,1) | (-2,1) | all 9 | 9 |
| (-1,1) | (-3,1) | all 9 | 9 |
| | | **Total** | **94** |

A standalone Node verifier that regenerates the closure and checks all transitions is in `paired_carry_94_closure.js`.

## 2. Source-root seed scan

A source-faithful replay of the #623 root recurrence was run through transition index 10,000. For each source state it used:

- the corrected mass-indexed buffer `B=34·ell+122`;
- the exact drain statistics `D,R` from the existing `sourceDrainStats` recurrence;
- the exact sector-specific `C,F) correction formulas in `SourceDerivedReset.lean`;
- both hypothetical L and R source-carry formulas, evaluated at the same source coordinates;
- the low input pair at position `k+1` to move the paired carry state to the start of the S-window at `k+2`.

For the 9,968 source transitions from index 33 onward, all 9,968 paired seeds lie in the 94-state closure; 86 distinct 94-states occur. Three transitions lie outside the original 66-state set, but are covered by the extension.

This is a finite replay, not a proof that every future authentic root seed lies in the 94-state set. The exact source-seed inclusion lemma is still open.

## 3. Universal output-reset diagnostic

For each of those 9,968 source windows, the input word consisted of digit pairs at positions `k+2,…,j-3`, with the additional high-end pair at `j-2` when `Δj=1`. It was passed through the paired transducer from **each of the 94 states**. The actual root branch was used, and `Δk` output symbols were trimmed to align the target S-window. The full reset DFA in `im-results/agent32-623-phase-automaton/ResetPatternDFA.json` then tested the target word.

Result: **9,967 of 9,968** source windows map to a reset-accepted target word from every one of the 94 possible paired starts.

The only exception is source transition `n=38`, sector RO / right branch. Starting from
`(px,py; L=(-1,0); R=(-2,1)) = (0,0;-1,0;-2,1)`
produces target word
`[1,2,1,5,6,6,6,6]`,
which the full reset DFA rejects. The actual source seed at `n=38` is
`(px,py; L=(0,0); R=(-2,0)) = (1,2;0,0;-2,0)`,
so the authentic paired start at this one transition passes.

The scan used `g>0` for L and `g<0` for R; the existing source-guard diagnostic reports no disagreement with the exact branch threshold over this finite prefix.

## 4. Mathematical significance and next steps

The 94-state closure is a compact carry-state space that includes the observed authentic source seeds, including the three cases missing from the 66-state invariant. It is a candidate basis for a smaller root-phase product.

The strongest next tasks are:

1. Formalize the 94-state transition closure in Lean, preferably with a finite state type and `decide`.
2. Prove that every authentic source paired carry after the low prefix belongs to this 94-state set, from the exact `C,F` formulas and root-coordinate/drain relations. The finite scan alone is not that proof.
3. Compose the 94-state paired transducer with the reset DFA and test whether a compact invariant closes on the authentic root language.
4. Resolve the isolated `n=38` universal-start counterexample by retaining the correlation between the root window and its actual paired carry seed; do not silently discard it.

This result is not suitable for `results/` yet. It belongs in `im-results/` until the source-seed inclusion and all-time closure are proved.
