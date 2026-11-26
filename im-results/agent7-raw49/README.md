# Raw49: universal sweeps and a source-accepted local frontier

Parent: `1RB---_1RC---_0RD---_1LD1RC_------_------`.

**Current accepted result.** The full Lean 4.36.0-rc2 source closure in [run 45882523160](https://github.com/FlareZ123/bb6/actions/runs/45882523160) proves `BB6.Agent7Raw49Progress.refined`: every machine TNF-quotient-compatible with this parent either satisfies `WeightedBound 7014` or belongs to an explicit list of **118 canonical residual cylinders**. The proof composes four universal sweep families with complete Covers for child indices C0, C2 and C5. The 118 residuals remain open. This is not a complete Raw49 parent Cover, not an accepted Canonical59 membership/removal, and not a BB(6) upper bound.

## Universal sweep families

At step 6 the blank orbit first queries C1. Four disjoint subfamilies are nonhalting for every completion:

- C1=0RC.
- C1=0RA, A1=0RC.
- C1=0RB, B1=0RC.
- C1=0RE, E1=0RC.

The common zipper family is C with nearest-first left list 111 (including the scanned symbol) and right list of 2n+1 ones. It is reached at step 6 for n=0. A rightward sweep erases pairs of ones (directly, or through the selected relay state); C0 enters D on a blank, then D0 rewrites the erased interval to ones while moving left. D1 turns right to C. The exact epoch length is 4n+8, and the next configuration belongs to n+1. The induction is independent of every unspecified slot.

`Raw49Sweep.lean` proves growth and universal `NeverHalts` with the repository SweepPumping semantics. The four subfamilies cover 25^6 + 3*25^5 = 273,437,500 distinct literal completions; this is not a count of quotient representatives or a full parent closure.

## Canonical cut and complete child Covers

`Raw49Cut.lean` integrates the sweeps with an audited canonical tree. Its finite audit has 125 open canonical cylinders; the four symbolic families reduce that list to 121. The source-accepted `parent_cut` theorem states that every TNF-quotient-compatible machine satisfies `WeightedBound 7014` or lies in the exact 121-entry residual list.

Three five-hole children of that residual list now have complete source-accepted Covers:

| Index in initial open list | Fixed A1 | Open leaves | Complete child proof |
|---|---|---:|---|
| 0 | 0LB | 14 = 13 FAR + 1 alternating sweep | `Raw49C0All.all_quotient` |
| 2 | 0RA | 56 = 53 FAR + 3 exact sweeps | `Raw49C2All.all_quotient` |
| 5 | 1LB | 21 = 21 FAR | `Raw49C5All.all_quotient` |

The exceptional C0 leaf is `1RB0LB_1RC0RE_0RD0LA_1LD1RC_1LF0RF_1LA---`. `Raw49Alternating.lean` proves at step 70 that F has left [0] and right (10)^3 1; each 40n+100-step epoch grows the exponent by two. Thus every F1 completion is nonhalting.

The three C2 exceptions are proved by `Raw49ThreeSweeps.lean`, with exact growth costs 6n+29 and 12n+29 (two variants). The FAR banks and symbolic exception map are checked by `gen_child.py`; it asserts that the open leaves are exactly the disjoint union of FAR-certified and theorem-certified tables.

`Raw49Progress.lean` composes the three child Covers with `Raw49Cut.parent_cut`. Lean proves the exact residual count 118 and the resulting conditional refinement. No unmatched child is discarded.

## Source acceptance and reproduction

Run [45882523160](https://github.com/FlareZ123/bb6/actions/runs/45882523160) regenerated the required source dependencies (`generate_sweeps.py`, `generate_four_hole.py`, and Agent10's `generate.py 66 70 80`), generated all three child proof trees, and compiled the complete transitive source closure at Lean 4.36.0-rc2. The explicit axiom audit passed for the root cut, all three child Covers, the 118-residual refinement and its count; the allowed profile is only `propext`, `Classical.choice`, and `Quot.sound`. The workflow rejects `sorryAx` and `native_decide`. This supersedes the earlier local-only check against a precompiled Canonical77 artifact.

To reproduce the generated child modules, run `bash prepare.sh /tmp/raw49-generated` from this directory after generating the three source dependencies above. The manual target `weighted-tnf-raw49-progress` in `.github/workflows/agent13-coverage.yml` performs the full source check. Generated Lean modules are intentionally not committed; the generators, FAR inputs, and source theorem are.

## Structure of the root-open frontier

Replaying the checked `Raw49Cut.tree` structurally, with the canonical cut index updated by each accepted destination state, recovers exactly 125 canonical open leaves. The first split is C1. Across those leaves, the second split is at A1 for 34, B1 for 26, and E1 for 64; one leaf is the direct C1=0RC sweep case and needs no second split.

The 125 leaves grouped by their first C1 assignment are:

| C1 move | Open leaves |
|---|---:|
| 0LA | 9 |
| 0LB | 6 |
| 0LE | 16 |
| 0RA | 6 |
| 0RB | 6 |
| 0RC | 1 |
| 0RE | 13 |
| 1LA | 12 |
| 1LB | 8 |
| 1LE | 19 |
| 1RA | 7 |
| 1RB | 6 |
| 1RE | 16 |

After removing the four universal sweeps and the C0/C2/C5 child Covers, the 118 residuals have this distribution:

| C1 move | Remaining |
|---|---:|
| 0LA | 6 |
| 0LB | 6 |
| 0LE | 16 |
| 0RA | 5 |
| 0RB | 5 |
| 0RE | 12 |
| 1LA | 12 |
| 1LB | 8 |
| 1LE | 19 |
| 1RA | 7 |
| 1RB | 6 |
| 1RE | 16 |

The completed depth-6 child-cut/FAR5 batch (run [45888550636](https://github.com/FlareZ123/bb6/actions/runs/45888550636), artifact 15150478430) covered 3,406 of 3,459 open leaves but left 53 exceptions across the six remaining C1=0LA siblings. Three of those siblings have only two exceptions each: C3 (148 FAR + 2 sweeps), C4 (299 FAR + 2 sweeps), C8 (593 FAR + 2 sweeps). The six missing tables now have locally kernel-checked universal nonhalting proofs in `Raw49SixSweeps.lean`, with standard axiom profiles only. The proof uses exact alternating-block growth (three variants, cost 12n+25; one variant, 12n+26) and one-block growth (two variants, costs 48n+85 and 24n+64). The original artifact FAR banks for C3/C4/C8 are preserved in `far3.txt`, `far4.txt`, `far8.txt`. The new `Raw49Progress115.lean` source is intended to compose these three complete child Covers with the accepted 118-residual theorem. Until the full source closure passes, the accepted count remains 118. The remaining C1=0LA children C1, C6, C7 had 25, 17, and 5 FAR5 exceptions respectively; no need to rerun that FAR5 bank.

## FAR5 diagnostic and remaining obligation

An exploratory max-5-state FAR search over all 125 root-open tables (run [45885525770](https://github.com/FlareZ123/bb6/actions/runs/45885525770)) reported exactly four FAR certificates. Those four tables are the same four already covered by the universal sweep families; it found no additional certificate among the 121 residuals. Consequently it did not improve the accepted 118-residual result. This is computational search output, not an additional accepted theorem. The first generated Lean integration exposed a Bool-orientation encoding error; the emitter now writes the correct Bool constructor, but the FAR5 module is deliberately not part of the accepted proof path because it produced no new coverage. Do not repeat the same max-5 search.

The remaining mathematical target is to close the 118 retained cylinders by a genuinely stronger method: discover new universal sweep/pump families or refine the hard residuals with a more powerful, evidence-backed search. Agent50 is evaluating a depth-3 FAR6 pipeline on the related Raw47 branch; wait for its actual new-certificate yield before considering a Raw49 adaptation. Agent31 has also been asked to check exact Raw49 membership in the current Canonical59 roster using the path alias `refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨true,true,2⟩)`. A complete parent Cover and exact roster membership are separate requirements before claiming a global frontier reduction.
