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
