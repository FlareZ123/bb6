# Raw107: complete source-certified six-hole cylinder

## Established result

Every completion of the partial table `1RB---_1RC---_0RD---_1LD1RE_---0RB_------` satisfies `WeightedBound 815` in the original weighted first-one semantics. This closes raw107 (canonical-124 index 72), including its six unassigned rows. The theorem is [Raw107ParentClosure.all_completions](Raw107ParentClosure.lean), and the original 124-cylinder residual list loses exactly one member in [Raw107RosterBridge.lean](Raw107RosterBridge.lean).

**Source acceptance:** [run 45533196624](https://github.com/FlareZ123/bb6/actions/runs/45533196624), head `1cea9dacc5a369bdd96a674486b642c45e7a59c4`, completed successfully at 03:21:28 UTC on 25 November 2026. The existing manual `raw107-parent` target executed the generator and complete import closure through Raw107RosterBridge under Lean 4.36.0-rc2; its `sorryAx|native_decide` log guard passed. The earlier [exception-witness run 45525124908](https://github.com/FlareZ123/bb6/actions/runs/45525124908) established the eleven special leaf nonhalting proofs. This is an original-source all-completions upper bound, not a proof that 815 is the least possible bound and not a universal BB(6) upper bound.

## Exhaustive first-hole split

The first undefined transition is B1 at ordinary time 7. [Raw107RootCut.lean](Raw107RootCut.lean) handles the halt alternative and eleven immediate side cycles; the remaining thirteen ordinary transitions use the following certified child bounds.

| B1 | Weighted bound | Original open leaves in discovery census |
|---|---:|---:|
| 0LE | 90 | 314 |
| 0LF | 815 | 1418 |
| 0RC | 200 | 392 |
| 0RD | 129 | 47 |
| 0RE | 201 | 258 |
| 0RF | 536 | 687 |
| 1LA | 282 | 1183 |
| 1LB | 212 | 588 |
| 1LC | 194 | 527 |
| 1LE | 231 | 840 |
| 1LF | 753 | 2497 |
| 1RE | 158 | 421 |
| 1RF | 160 | 569 |

Each five-hole child represents 25^5 raw row assignments under the discovery enumerator; the entire six-hole parent represents 25^6 = 244,140,625 assignments. These are raw assignment counts, not state-permutation quotient counts. The proof uses the actual compatibility predicate and exhaustive row split, rather than relying on counts.

The final exceptional leaf witnesses use explicit universal recurrences or source-level nonhalting bridges. The seven 1LA leaves and 1LA/385 are composed in [Agent1's bridge](../agent1-raw107/Raw107LABridge.lean); 0LF/180 uses [Raw107LF180Bridge](Raw107LF180Bridge.lean), and the two 1LF exceptions use [Raw107LFBridge](Raw107LFBridge.lean). Earlier exponential countdown and count-up, multi-block sweep and long-epoch recurrence discoveries remain in the local Lean modules and [historical discovery dossier](candidate-discovery.md). The eleven exceptions are no longer open.

## Consuming the accepted cylinder

The accepted raw roster bridge establishes the 123-entry residual dichotomy at 815 and at 7014, starting from the original 124 list. Its result overlaps the separate Combined106 and Canonical78 frontiers; counts must not be added.

[Raw107CanonicalGraft.lean](Raw107CanonicalGraft.lean) is a new direct source draft for the current 78-representative quotient frontier. It filters only the exact table of raw107, invokes `quotientSafe` with the source-accepted parent theorem, lifts 815 to 7014, and retains every other quotient-compatible entry. Its expected count is 77. The mixed-bound interface requires the remaining Covers at target B, with an independent attaining raw witness for exactness. The abstract filter/transport proof shape was compiled locally with Lean 4.36.0-rc2; the actual full source import closure and concrete count of 77 still require acceptance. Do not replace the accepted 78-count global interface before that check passes.

## Reproduction

Reuse the existing manual workflow [agent10-four-hole.yml](../../.github/workflows/agent10-four-hole.yml), target `raw107-parent`. It regenerates the ten child modules plus the three formerly conditional children, chunks each certificate, compiles Raw107RosterBridge through its actual dependency graph, and checks exported axiom profiles. The generator scripts, bank, specs and hand-written recurrence proofs are in this directory. The original discovery notes include roster hashes, exact exceptional tables, growth formulas and finite census details; their pending-status language is historical and superseded by the accepted parent run.

The remaining global objective is to consume this accepted certificate in the active quotient frontier, then resolve its retained residuals at the exact champion score.
