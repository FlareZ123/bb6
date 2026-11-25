# Rooted TNF coverage: seven certified parent cylinders

## Current claim and scope

The source proof target is a weighted first-one coverage dichotomy for every completion of the root `A0 = 1RB`: either its weighted halting bound is at most 7014, or its normalized transition table matches a member of an explicitly retained residual roster. This is an intermediate coverage reduction, not an upper bound for BB(6).

The seven endpoint cylinders already have individual source certificates: Agent 50's pilot (84), and the six Cryptids sibling parents r1 (7014), r2 (471), r3 (1768), r4 (42), r5 (28), r6 (582). The local replay confirms that their paths share prefixes; the trie has 52 first-hole expansions, seven closed endpoints, and 1190 off-path residual cylinders. Each expansion retains all 24 ordinary transitions and charges its halt child through the existing weighted blank-delay theorem.

A side-cycle reduction then identifies 388 exact packed residual tables whose entire completion cylinders are nonhalting. All 388 finite checker instances passed local Lean 4.36.0-rc2 against definition-identical executable side-cycle definitions; the residual count is 802. The generic coverage proof was also preflighted against local imported-interface fixtures. These fixtures are not a substitute for checking the original imports; the full source audit is [run 45457603529](https://github.com/FlareZ123/bb6/actions/runs/45457603529), queued at commit `b983329d3ab7bb065b3a51c2d773715d400d7adb`.

## Proof and reproducibility

- [SevenRoster.lean](SevenRoster.lean): exact packed-table replacement, checked path expansion, endpoint erasure, and `sevenRoster_sound`. No proof-constructor evaluation is required for roster production. The semantic dichotomy refers to the actual list, not its diagnostic cardinality.
- [SevenSideWitnesses.lean](SevenSideWitnesses.lean): 388 literal certificates; source checker soundness discharges each table, and `reducedSevenRoster_sound` retains every unmatched table. Matching uses full twelve-slot equality, not hashes or positional assumptions.
- [replay_seven.cjs](replay_seven.cjs): independently replay the seven paths and generate side-cycle candidates (300-step search cap; maximum successful witness endpoint 168). Run `node replay_seven.cjs > seven-side-data.lean`. Candidate certificates are checked by Lean; the search is not trusted.
- [RootFrontierR1R4.lean](RootFrontierR1R4.lean): earlier three-parent dependent proof-tree approach. Its implicit move arguments were corrected after the prior source audit failed before reaching the shard; the packed roster supersedes it as the scalable computational interface.

The separate root certificate, weighted delay accounting, and all ordinary child completeness proofs are reused from existing source modules rather than replaced by new assumptions. Prior individual graft acceptance is documented in the [shared source audit](https://github.com/FlareZ123/bb6/actions/runs/45422023863). No claim is made that every side-cycle witness is new relative to the other agents' overlapping rosters.

## Open obligations

The residual roster must be reduced further or matched to complete independently certified source enumeration coverage. Agent 50's recursive partial-tree checker is a suitable next reduction interface. A local experimental scan of the 83 two-hole unresolved cylinders found 66 with an observed first hole within 300 steps. Nineteen have complete candidate closures; the remaining 47 have partial candidate reductions. These are experimental until checked, and 17 cylinders have no observed first hole or side-cycle witness within that cap. Coverage of this rooted raw-label shard alone does not establish the global maximality bound.

## 2026-11-25: source-audited component cuts and 19-sibling expansion (work in progress)

This work is a separate first-one residual-roster line. It should not be conflated with the earlier 802-entry ray-reduced frontier described above.

### Source-audited component cuts

Three component groups now have successful Lean source-closure audits:

- `FiveHoleRoster`: raw66/70/80, weighted bound 395 (liftable to 7014); source audit run [455137](https://github.com/FlareZ123/bb6/actions/runs/45513767248).
- `AllTwelveRoster`: raw86/87/88/91/92/93/97/98/100/101/102/104, weighted bound 7014; source audit run [454903](https://github.com/FlareZ123/bb6/actions/runs/45490350737).
- `NewFiveRoster`: raw68/72/82, weighted bound 7014; source audit run [45515691855](https://github.com/FlareZ123/bb6/actions/runs/45515691855).

The three groups are proposed as a disjoint 18-cylinder cut from the 124-entry `remainingRootRoster`. The two-group composition `Combined109Roster.lean` is now source-accepted: [run 45515820680](https://github.com/FlareZ123/bb6/actions/runs/45515820680) succeeded. It kernel-checks the 15-cylinder union and 109-entry remainder, plus conditional cover/TNF/ExactBB6 interfaces at weighted bound 7014. The three-group composition `Combined106Roster.lean` adds NewFiveRoster and asks Lean to prove pairwise disjointness, the 18-entry union, and the 106-entry remainder. Its audit [45518426903](https://github.com/FlareZ123/bb6/actions/runs/45518426903) succeeded: the raw 106-residual dichotomy is source-accepted. The same-threshold wrappers do not suffice for a larger champion B; residual Covers must instead be at B.

### First-hole expansion of the 19 depth-10 siblings

A bounded simulator sweep over raw residual indices 0, 2, 4, 6, 8, 9, 10, and 149–160 found 92 candidate ordinary nonhalting children (11 exact lassos and 81 half-line side cycles), plus 19 immediate-halt children, leaving 364 ordinary nine-hole children. Reproducible candidate data and script:

- `root-sibling-first-hole-sweep.json`
- `root-sibling-first-hole-sweep.mjs`

The formal draft `RootSiblingFirstHole.lean` replays all 92 candidates through `residualWitnessOK`, proves the first-hole halt-delay conditions for the 19 parents, and aims to establish the 364-entry local residual roster and its exact mass identity. Run [45522135654](https://github.com/FlareZ123/bb6/actions/runs/45522135654) failed because `rootSiblingKnownRunTwo` omitted `initialSlot` and the older source still used an unavailable tactic. The proof was patched and corrected rerun [45522855534](https://github.com/FlareZ123/bb6/actions/runs/45522855534) failed only on an extra tactic after the mass identity had already closed. That tactic has been removed, and the revised generic exact-table replacement proof was preflighted with local interface fixtures. A new full source audit is dispatched. Earlier runs [45521979334](https://github.com/FlareZ123/bb6/actions/runs/45521979334) and 45522135654 are superseded. **All 92 candidates remain heuristic until the corrected Lean target passes.**

Conditional on the proposed 106-roster composition, the 19 ten-hole siblings account for 96.4443% of its completion mass. If all 92 witnesses and 19 halt branches validate, their expansion would reduce the proposed global unresolved mass by 22.5375%. These are exact arithmetic calculations over the canonical roster, not yet a formal global-roster replacement theorem.

The smaller concrete example `RootZeroRefinement.lean` builds a `RootedFrontier` for B0=0LA, closing seven ordinary children and the halt child while retaining 17 children. Its first audit [45518681714](https://github.com/FlareZ123/bb6/actions/runs/45518681714) failed on root unfolding, residuals namespace, and unavailable norm_num tactic. The repair rerun [45521974375](https://github.com/FlareZ123/bb6/actions/runs/45521974375) also failed: the post-A0 known-run simplification and generic root-preservation proof remain incomplete, and the residual-membership proof needs an explicit list change. Do not treat RootZero as source-accepted.

### Other audit status

The rooted R1/R4 shard and its 388 side-witness integration compiled in [run 45514421095](https://github.com/FlareZ123/bb6/actions/runs/45514421095). That workflow failed later in `BB6Agent42/ExceptionalPumps.lean:20:9` with the blank/emptyAt mismatch and `sorryAx` in the ExceptionalPumps nonhalting theorems. Do not treat that unrelated pump module as accepted; the R1/R4 compile itself succeeded.

None of these conditional frontiers establishes an unconditional BB(6) upper bound. The outstanding task remains to prove a uniform bound for every residual cylinder, or otherwise close the complete root frontier.

## Canonical state-introduction frontier (new draft, 2026-11-25)

The raw rooted tree need not be invariant under arbitrary permutations. Instead, normalize fresh labels at **each actual first hole**, extending the current introduced-state cut. The existing source-accepted `tnf_branch_frontier` preserves quotient compatibility under root-fixing state permutations. Induction on the original RootedFrontier then yields either its early weighted bound or a residual with canonical address and quotient compatibility. Already closed branches transfer their bound under the permutation. This uses the actual path, not an assumption that a renamed raw residual is another member of the old roster.

- [CanonicalFrontier.lean](CanonicalFrontier.lean) implements the generic induction, 96-candidate canonical remainder, and mixed-bound cover composition.
- [Canonical78Roster.lean](Canonical78Roster.lean) applies the accepted 18-cylinder cut to that remainder, with a candidate count of 78. The final interface takes residual Covers at the target B (not at 7014) and the attained B witness.

The deterministic manifest census gives 124 raw residuals -> 96 canonical addresses -> 78 after the 18 accepted removals. The 28 discarded raw indices are 126–129, 135–138, 141–160. This is a representative-count reduction, not a reduction in physical completion mass. Generic induction and sibling-refinement proof shapes were locally preflighted against fixtures; the new modules still need original-source audits. Manual targets `weighted-tnf-canonical-frontier` and `weighted-tnf-canonical-78` have been dispatched. Do not use the 78 count as a kernel-accepted theorem until that audit succeeds.

The champion-compatible raw139 is retained. Exact BB(6) remains open; this construction only reduces the number of residual safety obligations for maximality.
