# Additional side-witness coverage in the canonical first-one frontier

**Status:** intermediate computational scan. This is not a complete cover of any parent and does not establish the BB(6) upper bound. It identifies reusable, already checked side-cycle cylinders under three additional first-one residuals.

## Method and exact source data

The scan reads:

- `im-results/agent47-rooted-tnf/SideWitnessCore.lean`, whose `witnesses_checked` theorem checks all 388 listed `SideWitness` certificates;
- `im-results/agent13-roster-convergence/canonical-124.json`, the exact 124-table first-one residual manifest.

The encoding is the one used by `SideWitnessCore`: 0 means wildcard in a certificate row; 1..24 identify ordinary transitions. A completed transition slot has 25 values: halt plus the 24 ordinary transitions. The script uses exact integer arithmetic and a memoized 25-way Shannon recursion to count unions; it does not enumerate (25^{10}) or (25^9) machines.

Run from the repository root:

```bash
python im-results/agent2-sidewitness-multiparent/scan.py
```

## Exact parent matches

| Raw residual | Canonical index | Address | Holes | Matching checked witnesses | Union coverage |
|---:|---:|---|---:|---:|---:|
| 8 | 4 | B0=0LC | 10 | 68 | 15,943,636,947,500 / 95,367,431,640,625 (16.718%) |
| 9 | 5 | B0=0RC | 10 | 108 | 31,473,123,262,500 / 95,367,431,640,625 (33.002%) |
| 10 | 6 | B0=1LC | 10 | 65 | 4,477,340,035,625 / 95,367,431,640,625 (4.695%) |
| 23 | 13 | B0=1RC, C0=0LD | 9 | 96 | 771,676,095,000 / 3,814,697,265,625 (20.229%) |

The script exhausts all 124 manifest entries before reporting these four hits: the 388-row SideWitnessCore pool has no direct refinement of the other 120 canonical-124 parents in this orientation. This is a statement about this certificate pool and this exact orientation only; it does not rule out certificates from other libraries or symmetry-transformed witnesses. Raw10 is included as a control and reproduces the existing Agent13 scan. Its union includes the 65 SideWitness cylinders and the separate q_i(2800,100) held leaf, which adds 25 disjoint completions. The other three rows count only SideWitness cylinders.

The four parent cylinders are pairwise disjoint first-one branches. Together their parent completion mass is 289,916,992,187,500; the combined checked-cylinder mass is 52,665,776,340,625 (18.166%). This aggregate is a bookkeeping sum over disjoint parents, not a claim that their complements are closed.

## Whole child branches already closed by single witnesses

Some matching witnesses fix exactly one slot beyond the parent, so they prove the entire corresponding child cylinder, not just a finite set of completions:

- **raw8:** C1 = 0LA, 0RA, 1RA, 1RB (four whole children);
- **raw9:** C0 = 0LA, 0RA, 1RA, 0LB, 0RB, 1RB, 0RC, 1RC (eight whole children);
- **raw10:** C1 = 0LA (already recorded in Agent13's pilot);
- **raw23:** D1 = 0RA, 1RA, 0RB, 1RB, 1RC (five whole children).

Each branch has a concrete row in `SideWitnessCore`; `SideWitness.hasWitness_sound` can transport the existing checked witness to the complete child cylinder. These 17 additional whole branches (raw8/raw9/raw23) are the most compact first Lean graft.

## Exact disjoint complements

Using Agent49's generic first-mismatch subtraction from `im-results/agent49-box-complement/BoxComplement.lean`, the deterministic sequential subtraction produces:

| Parent | Certificates subtracted | Disjoint residual rectangles | Residual completion mass |
|---:|---:|---:|---:|
| raw8 | 68 | 208 | 79,423,794,693,125 |
| raw9 | 108 | 108 | 63,894,308,378,125 |
| raw10 | 65 + held leaf | 34 | 90,890,091,604,975 |
| raw23 | 96 | 12,584 | 3,043,021,170,625 |

The residual rectangles are exact obligations: a machine in the parent that matches none of the consumed certificates lies in exactly one rectangle. The generic Lean theorem `subtractMany_exact` proves the complement equivalence, and `subtractMany_disjoint` proves pairwise disjointness. The raw10 adapter demonstrates how to turn the residual boxes into a conditional `Cover` and feed it to the canonical78 consumer.

Raw9 is the best next complete box-consumer target (108 residual boxes and 33.002% of its parent already certified), followed by raw8 (208 boxes). Raw23's 12,584-box first-mismatch complement is too fragmented for a naive list consumer; it should use a reduced multi-valued decision diagram or a smaller selected certificate subset.

## Reduced multi-valued decision diagrams

The same unions also admit a much smaller reduced 25-way decision DAG. The committed node tables are in `bdds.json`; terminal ID 0 means open (not matched by any consumed certificate), terminal ID 1 means covered. Each internal node tests one still-unfixed transition slot and has 25 children, one for halt and each ordinary move. The generator chooses the most discriminating remaining slot, memoizes recursion states, and hash-conses identical nodes.

| Parent | Memoized states | Reduced internal nodes | First-mismatch rectangles |
|---:|---:|---:|---:|
| raw8 | 23 | 19 | 208 |
| raw9 | 45 | 37 | 108 |
| raw10 (65 witnesses + held leaf) | 49 | 27 | 34 |
| raw23 | 74 | 31 | 12,584 |

In particular, raw23's 12,584 disjoint rectangles collapse to a 31-node DAG. This is an exact computational representation of the same union/complement, not yet a Lean kernel-checked theorem. It is a much better target for a compact formal checker than materializing every first-mismatch rectangle. The updated `scan.py` reconstructs each DAG and checks its complete node table against `bdds.json`.


## Roster status and proof boundary

The manifest identifies raw8/raw9/raw23 as canonical indices 4/5/13. None is among the 18 exact cylinders removed by `Combined106Roster.covered` (raw66/70/80; raw86/87/88/91/92/93/97/98/100/101/102/104; raw68/72/82), and their addresses satisfy the first-one state-introduction rule. They are therefore expected to be retained canonical78 obligations. A Lean exact-membership theorem is still required before treating this as an accepted roster graft.

No parent is closed by this scan. Every residual rectangle in the table above remains an obligation at the champion score. The safe result is only that each consumed side-witness cylinder has `WeightedBound 7014`, by the existing kernel-checked `SideWitness.sound`; this bound can be lifted monotonically to the champion score. The next proof-bearing step is a Lean module that proves exact canonical78 membership, derives the parent-specific witness lists and their safety, and consumes the disjoint complements without losing any open rectangle.
