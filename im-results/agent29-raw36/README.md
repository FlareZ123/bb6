# Raw36: large first-hole branch and state-symmetry reduction

**Status: computational candidate partition; source-level certification incomplete.** Raw36 is the eight-hole parent `1RB---_1RC---_0RD---_0LD---_------_------`. Its first undefined query is D1 at primitive step 5. The canonical `Raw36Cut.lean` proposes a sound quotient cut: ten D1 ordinary choices close by direct translated cycles; D1=1LB first reaches B1, where five additional direct cycles close. The remaining parent children are explicitly retained as obligations. This is **not** a Raw36 parent Cover and is **not** a BB(6) maximality proof.

## Candidate complete descendant and original-source proof route

The six-hole descendant `1RB---_1RC0LA_0RD---_0LD1LB_------_------` first queries C1 at step 9. The exhaustive first-hole search (`candidate.json` and `search.cjs`) reports, over all 25^6 = **244,140,625** literal total completions:

| Status in untrusted candidate classifier | Literal completions |
| --- | ---: |
| Halting | 20,583,715 |
| Nonhalting | 223,556,910 |
| OPEN | 0 |
| **Total** | **244,140,625** |

The 24 ordinary C1 branches have 395,640 candidate nodes: 16,484 splits, 288,336 translated cycles, 10,830 FAR closures and 79,990 last-slot closures. The reported sufficient weighted bound is **162**, including incoming blank delay; it is not asserted sharp. All statements above are deterministic generator claims, **not** Lean-certified bounds until their original-source child checks compile.

`generate.py` reconstructs each selected branch independently from the exact table, verifies its expected search statistics, emits Lean `Audit` terms, and factors large audit trees through the existing chunking utility. A full invocation now emits a `Raw36Branch.lean` composer referencing the selected representative child proofs. The existing manual `agent10-four-hole.yml` selector `raw36-pilot` performs a narrow original-source compilation of `Raw36Kid01.kid01_bound`; run [46073656511](https://github.com/FlareZ123/bb6/actions/runs/46073656511) was dispatched against revision `a6922000f5446849adcf2d05c1cbe14d92645db0`. Its result must be checked before asserting proof acceptance.

### Exact E/F symmetry and certificate-size saving

E and F are unused in this six-hole branch before C1 is assigned. `Raw36Symmetry.lean` defines their state transposition and derives a branch-specific conditional transport:

```lean
theorem childF_bound (B : Nat) (w r : Bool)
    (h : ∀ m, compatible (child ⟨w,r,4⟩) m → WeightedBound B m)
    (m : Machine) (hm : compatible (child ⟨w,r,5⟩) m) :
    WeightedBound B m
```

The argument uses the existing source `rename_compatible_unused`, `firstOne_terminal`, and `weighted_rename_back`; its trust is precisely that of those source theorems **if the new bridge compiles**. The new bridge has not yet passed a source audit. It is included as an additional root in subsequent `raw36-pilot` dispatches, without new workflow creation.

Accordingly, the generator no longer reconstructs the four F-target audits (C1 choices 0LF, 0RF, 1LF, 1RF). The F children are supplied by `childF_bound` from 0LE, 0RE, 1LE, 1RE in the final composer. This preserves all 24 ordinary branches while reducing the generated candidate trees from **395,640 to 256,436 nodes**, a saving of **139,204 nodes (35.18%)** before Lean compilation. These are source-code and deterministic-count properties, not accepted math until the combined proof compiles. The machine equivalence is a genuine universal state relabeling, not an empirical equality of the four search outputs.

## D1=1LB seven-hole candidate closure

The three B1 follow-up JSON collections also record the other ten ordinary B1 descendants and four fresh-label descendants with no OPEN nodes. Together with B1=0LA (`candidate.json`), the five direct cycles, B1 halt, and four E/F symmetry aliases, they purport to exhaust the entire D1=1LB cylinder. Candidate literal-completion census:

| Status | Completions |
| --- | ---: |
| Halting | 615,712,761 |
| Nonhalting | 5,487,802,864 |
| **Total** | **6,103,515,625 = 25^7** |
| OPEN | 0 |

The 15 searched canonical B1 branches have 4,862,174 candidate nodes, excluding their early cuts. Sufficient candidate weighted cutoff **166**. Fresh-E/F multiplicity-two branches are B1=0LE, 0RE, 1LE and 1RE; the other eleven branches have multiplicity one. These census and bound claims remain computational candidates pending formally checked source certificates.

## Missing theorem and next decision

1. Check `Raw36Cut`, the E/F transport and the first generated child on the existing manual original-source CI target; repair actual compiler diagnostics, without rerunning candidate discovery.
2. Source-certify the remaining representative C1 child proofs using bounded groups and strict imported-object manifests, then compile `Raw36Branch.branch_bound` at 162. This would close one six-hole descendant, **not yet D1=1LB**.
3. Compose the other B1 descendant proofs, the explicit B1 transition partition and the E/F relabelings to cover D1=1LB at 166. Finally address the other retained D1 cylinders and its exact current canonical roster membership. There is no valid global roster deletion yet.

Three earlier pilot failures were generation/integration defects (metadata alignment, parser terminator formatting, and missing imports), not falsifications of the candidate mathematical partition. The corrected source and experimental JSON are retained here. Do not confuse zero OPEN in search output with a kernel-certified universal bound.
