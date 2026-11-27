# Raw49: universal sweeps and a source-accepted local frontier

Parent: `1RB---_1RC---_0RD---_1LD1RC_------_------`.

**Current accepted result.** The full Lean 4.36.0-rc2 source closure in [run 45908176789](https://github.com/FlareZ123/bb6/actions/runs/45908176789), artifact 15158569727, proves `BB6.Agent7Raw49Progress115.refined`: every machine TNF-quotient-compatible with this parent either satisfies `WeightedBound 7014` or belongs to an explicit list of **115 canonical residual cylinders**. Six child Covers (C0, C2, C3, C4, C5, C8) and four root sweeps are composed. The 115 residuals remain open at the accepted parent-level theorem. This is not a complete Raw49 parent Cover, not an accepted canonical-roster removal, and not a BB(6) upper bound.

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

The completed depth-6 child-cut/FAR5 batch (run [45888550636](https://github.com/FlareZ123/bb6/actions/runs/45888550636), artifact 15150478430) covered 3,406 of 3,459 open leaves but left 53 exceptions across the six remaining C1=0LA siblings. Three of those siblings have only two exceptions each: C3 (148 FAR + 2 sweeps), C4 (299 FAR + 2 sweeps), C8 (593 FAR + 2 sweeps). The six missing tables are proved nonhalting by `Raw49SixSweeps.lean`, using exact alternating-block and one-block growth. Their FAR banks are preserved in far3/4/8.txt. The consumer `Raw49Progress115.lean` passed the full source gate in run 45908176789: refined uses [propext, Classical.choice, Quot.sound] and residual_count uses [propext]. No need to rerun the FAR5 bank.

## New leaf certificates (local Lean checks)

The remaining C1/C6/C7 subtrees had 25/17/5 FAR5 exceptions. C7 has five locally proved sweeps in `Raw49C7Sweeps.lean`; C1 has ten guard cases in `Raw49C1Guard.lean` from the preceding investigation. The archived search was extended only on the other 32 exceptions. Two new modules compile against the source-accepted dependency objects from artifact 15158569727:

- `Raw49AutoSweeps.lean`: ten exact blank-entry and uniform growth proofs, four C1 (M112, M113, M116, M118) and six C6 (M603, M604, M607, M609, M610, M616), each exporting a universal NeverHalts theorem with only propext and Quot.sound. The symbolic zipper synthesis handles fixed frames, repeated words, and the two variable blocks of M604. Each theorem includes an exact cost and a positive growth recurrence.
- `Raw49MutatedFAR.lean`: 18 explicit FAR certificates discovered by mutation of archived DFA seeds, ten C1 and eight C6. Every certificate passes fastValid with kernel reduction, and every NeverHalts theorem has only propext, Classical.choice, Quot.sound. The certificate data and complete table are embedded in source; the mutation search is not trusted.

The final C1 exception M122 = `1RB0LE_1RC0LF_0RD0LA_1LD1RC_1RA1RE_---1LB` is now locally proved by `Raw49Doubling.lean`. The blank orbit at step 15 reaches B with empty left tape and right (10)^2, and the universal return sends (10)^n to (10)^(2n+1) for n >= 2. The proof uses two nested sweeps, with the inner induction reducing the remaining zero delimiters and increasing the produced exponent by two.

**All C6 exceptions now have local source-import Lean proofs.** `Raw49C6Counters.lean` contains:
- M600: blank entry at 58; a three-phase B/C/E invariant uses aligned left pairs (odd bit implies even bit) and right pairs (odd bit zero), including finite-list padding. This proves arbitrarily long live prefixes without analyzing exponentially long counter epochs.
- M608: blank entry at 10; a two-parameter alternating-gap family G(k,l) transfers one pair, and outer O(k) returns to O(2k+4). Exact finite costs and positive returns yield universal nonhalting.
- M613: blank entry at 8; the right tape encodes a little-endian counter with bit b encoded as b0b0 and sentinel 101. A recursively proved carry increments the list, including overflow, with positive exact cost. F1 is never queried.

All three `never` exports passed Lean 4.36.0-rc2 against actual accepted SweepPumping dependency objects from artifact 15158569727, each using [propext, Quot.sound]. The archived 1478 FAR certificates are preserved in far6.txt. C6 has 1495 leaves = 1478 FAR5 + 8 mutated FAR + 6 exact sweeps + 3 counters/invariants. The C1 (714 FAR5 + 10 guard + 10 FAR + 4 linear sweeps + 1 doubling) and C7 (174 FAR5 + 5 sweeps) generators are retained. The new C6 generator and `Raw49Progress112.lean` compose with Progress113 to target 112 residuals. Full source acceptance remains pending; 115 is the last confirmed accepted count.


## FAR5 diagnostic and remaining obligation

An exploratory max-5-state FAR search over all 125 root-open tables (run [45885525770](https://github.com/FlareZ123/bb6/actions/runs/45885525770)) reported exactly four FAR certificates. Those four tables are the same four already covered by the universal sweep families; it found no additional certificate among the 121 residuals. Consequently it did not improve the accepted 118-residual result. This is computational search output, not an additional accepted theorem. The first generated Lean integration exposed a Bool-orientation encoding error; the emitter now writes the correct Bool constructor, but the FAR5 module is deliberately not part of the accepted proof path because it produced no new coverage. Do not repeat the same max-5 search.

The remaining mathematical target is to close the 115 retained cylinders by a genuinely stronger method: discover new universal sweep/pump families or refine the hard residuals with a more powerful, evidence-backed search. Agent50 is evaluating a depth-3 FAR6 pipeline on the related Raw47 branch; wait for its actual new-certificate yield before considering a Raw49 adaptation. Agent31 has also been asked to check exact Raw49 membership in the current Canonical59 roster using the path alias `refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨true,true,2⟩)`. A complete parent Cover and exact roster membership are separate requirements before claiming a global frontier reduction.

## C9–C14 candidate closure (2026-11-27)

The six C1=0LB root siblings have 3424 depth-six open cylinders, of which 3407 have explicit FAR certificates (3361 initial seed/FAR5 certificates, 46 targeted mutations), and all remaining 17 have exact universal nonhalting theorems in `Raw49NextSweeps.lean`. The latter passed Lean 4.36.0-rc2 against the source-accepted SweepPumping dependency closure (all [propext, Quot.sound]). Five siblings' counts plus C13: C9 307+12, C10 647+0, C11 173+2, C12 176+0, C13 1557+3, C14 547+0. All banks are stored as far9.txt through far14.txt. The sweep synthesis uses finite opaque-tail block transfers, exact entry, a universally quantified one-block `rfl` lemma, sweepL/R, exact arithmetic and word rotation (`commute_rep`), followed by `never_of_growth`. Two novel two-block families (M90111, M90217) simultaneously extend (00)^n and (01)^n; costs 12n+26 and 12n+22, entries 18 and 14. `Raw49Progress106.lean` composes the candidate six Covers with Progress112; the source gate has not yet run for this candidate. No global roster claim.

## C15–C26 discovery, compact reproducible certificates (2026-11-27)

A new batch has 6441 open leaves; exact seed-pool replay with 166 distinct automata (no exhaustive FAR enumeration) covers 6366. The 72 remaining sweep proofs are encoded in sweep_recipes.jsonl and expanded by emit_sweep_recipes.py. All 72 compiled under Lean 4.36.0-rc2 with the actual source-accepted SweepPumping dependency objects, with [propext, Quot.sound]. Recipes express opaque-tail fixed-step transfers, affine sweep costs and exact word commutations; two variable blocks supported. The three leaves still outside these certificates are M150478 (candidate asymmetric RLE stack abstraction, parameters left 6,3,2 right 7,3,2; 3115 abstract configurations), M230574 and M261066. C16/17/18/19/20/21/22/24/25 are certificate-complete; Progress97 composes their Covers with Progress106. Pending full source gate. C15/23/26 are not removed. No global roster deletion. Certificate pools are deliberately replayed rather than storing repeated assignments: the same 6366 leaves were covered in local deterministic replay. The checker still verifies every individual chosen FAR proof.

## 2026-11-27T19:01Z: accepted 112 and new 58 candidate

Source gate 46049845768 succeeded for Progress112, artifact 15224693544. Progress97 gate dispatched at 47e890763bd43e9e6b84c52891eaa133168320be. The new batch C27–C124 contains 62152 open cylinders; 60796 are reproduced by the union of 261 FAR automata, seed replay only. Three exact sweep proof recipes passed kernel checking. Seven RLE proof recipes (including C15/M150478) passed against the exact TwoSidedAutomata closure of accepted run 45829435208 artifact 15121597506, with standard axioms [propext, Classical.choice, Quot.sound]. Quotient reduced M150478 from 3115 to 679 states; six other certificates reduce to 234,198,230,94,193,230. Original large certificate timed out; quotient replay succeeded. C15 and 38 new C27–C124 children are candidate complete; Progress58 composes them with 97. Remaining 1347 uncovered leaves in latter batch, plus M230574/M261066. Four already-resolved direct roots C32/C38/C43/C47 not counted as new. Full canonical Cover source proof still pending for the new 58 count. No claim of global roster deletion. The seed additions and RLE/sweep recipes are persisted; avoid repeated searches. Exact 38-child list: 29, 44, 48, 52, 54, 55, 57, 60, 61, 62, 64, 65, 67, 68, 69, 70, 73, 74, 75, 76, 77, 78, 82, 83, 84, 85, 86, 88, 89, 93, 94, 100, 105, 111, 114, 115, 119, 123.
