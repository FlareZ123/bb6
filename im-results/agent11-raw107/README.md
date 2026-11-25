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

The canonical 78 roster contains raw107 and raw114 as distinct representatives. Both now have complete original-source parent bounds:

- **raw107:** `Raw107ParentClosure.all_completions` proves `WeightedBound 815` for every completion of `1RB---_1RC---_0RD---_1LD1RE_---0RB_------`; source audit [45533196624](https://github.com/FlareZ123/bb6/actions/runs/45533196624) passed at proof-source head `1cea9dacc5a369bdd96a674486b642c45e7a59c4).
- **raw114:** `BB6.Agent47Raw114Complete.raw114_all` proves `WeightedBound 7014` for every completion of `1RB---_1RC---_0RD---_1LD1RE_---0LD_------`; full source audit [45553564319](https://github.com/FlareZ123/bb6/actions/runs/45553564319) passed at pinned proof-source revision `d4164a4457e62ba7ec8e3fba6e38b251d04ffc83`.

These are overlapping views of the same global frontier, not additive completion counts. The accepted raw roster bridge removes raw107 from the 124-entry list (123 remain); the canonical quotient interface is a separate 78-entry list.

Agent47's [CanonicalTwoParentGraft.lean](../agent47-rooted-tnf/CanonicalTwoParentGraft.lean) defines the exact canonical parents `p107` and `p114`, proves the generic 78→77→76 roster counts, and supplies `roster76_sound` and `exact_at_target` conditional on both parent bounds and Covers for every one of the 76 retained representatives. The current [CanonicalRaw114Accepted.lean](../agent47-rooted-tnf/CanonicalRaw114Accepted.lean) wrapper instantiates raw114 alone; its graft workflow run [45554648116](https://github.com/FlareZ123/bb6/actions/runs/45554648116) does not by itself instantiate raw107.

The new [CanonicalTwoParentAccepted.lean](CanonicalTwoParentAccepted.lean) instantiates raw107 by proving the finite table equality `p107 = BB6.Agent10Raw107Root.parent`, then combines the accepted raw107 bound with the raw114 wrapper. It exposes the 76-residual dichotomy and conditional exactness while retaining all 76 Covers. **This is a source-audit draft, not yet an accepted two-parent theorem.** The earlier [Raw107CanonicalGraft.lean](Raw107CanonicalGraft.lean) is retained as the historical one-parent draft and is superseded by the shared two-parent construction.

There is currently no downloadable `.olean` artifact for raw107 (run 45533196624 uploaded none). The raw114 certified-root artifact is available from run 45553564319. For a reproducible combined audit, compile raw107 at the same pinned d416 source revision, compare complete shared-module source/import/compiled hashes, and reject unexplained collisions. The extended [Lean closure helper](../../tools/lean_compile_closure.py) now supports source/import/olean manifests and compatibility comparisons; its integration into the graft workflow remains pending.

## Reproduction

Reuse the existing manual workflow [agent10-four-hole.yml](../../.github/workflows/agent10-four-hole.yml), target `raw107-parent`. It regenerates the ten child modules plus the three formerly conditional children, chunks each certificate, compiles Raw107RosterBridge through its actual dependency graph, and checks exported axiom profiles. The generator scripts, bank, specs and hand-written recurrence proofs are in this directory. The original discovery notes include roster hashes, exact exceptional tables, growth formulas and finite census details; their pending-status language is historical and superseded by the accepted parent run.

The remaining global objective is to consume this accepted certificate in the active quotient frontier, then resolve its retained residuals at the exact champion score.
