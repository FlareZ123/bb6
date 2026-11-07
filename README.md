# BB(6) research

Collaborative research toward a rigorous determination of the six-state, two-symbol, blank-tape Busy Beaver **step** value. This repository contains original-machine formalizations, mathematical reductions, inverse and forward invariants, finite checks, and experimental leads.

**Research state (6 November 2026): BB(6) is unresolved.** No complete blank-start halt/nonhalt decision for all remaining machines, exhaustive six-state maximality certificate, or exact maximal runtime proof has been established here. Individual source-verified reductions have narrower mathematical scope than a machine decision.

## Start here

| Document | Purpose |
| --- | --- |
| [Results map](results/README.md) | Established statements, verification scope, and missing global proof obligations |
| [Research board](research/BOARD.md) | Research questions, bottlenecks, and primary dossiers |
| [Research guide](RESEARCH_PROTOCOL.md) | Scientific practice and continuity |
| [Investigation notes](research/issues/README.md) | Research questions with historical context |
| [Reference resources](resources/START_HERE.md) | Source context and orientation |
| [Agent guidance](AGENTS.md) | Repository-specific agent instructions |

## Main proof gaps

- **Machine C:** The source-exact fixed-target root decision is now integrated with four additional infinite low/high exclusions, including a source-certified 27/0 branch with M512-admitted members. The parameter existential remains unbounded, so BB(6) is unresolved. [Integrated criterion and evidence](im-results/agent19-c-odd-dyadic/JointCriterionIntegration.md) · [Lean theorem](im-results/agent3-c-bounce-inverse/ValSixJointFull.lean) · [Agent19 research map](im-results/agent19-c-odd-dyadic/README.md).
- **P1:** Original-source critical-gateway exclusions, reset-count bounds, and affine-wall cost barriers constrain infinite families. Surviving inverse exits and actual blank-root reachability remain unresolved. [P1 results](results/README.md) · [cost wall](im-results/agent43-p1-high-cost-reset-count/README.md).
- **#429 and #746:** Source-connected halting-gate reductions and inverse grammars narrow the questions while leaving unbounded blank-root reachability open. [#429](im-results/agent6-harmonic429/README.md) · [#746](im-results/agent10-cascade/README.md).
- **Cryptid D, Sheep, and other roots:** Conditional return grammars, source-proved local branches, and finite continuations require a complete physical blank-root invariant, witness, or exclusion. [D](im-results/agent2-cryptid-continuity/README.md) · [Sheep](im-results/agent22-sheep-mixed-hub/README.md).
- **Global completeness:** The source-sound physical-trace, exact-lasso and finite-entry-macro tree reports **68.066560%** classified raw tables at depth four by interpreted Lean VM; its soundness and total-mass conservation are kernel proved, but the numeric cardinality is not separately proved in the kernel. A distinct independently audited six-row-plus-lasso union reports **60.328335360%**; the reports overlap and cannot be added. A bounded lasso/macro screen of the frozen 663 historical holdouts yielded **zero hits**. **Machine C and #623 now have authentic, source-checked paths into explicitly open depth-four leaves**, giving concrete targets for all-time root closure while deciding neither machine. No exhaustive six-state closure or exact champion score is established. [Global dossier](im-results/agent32-zero-prefix-global/README.md) · [Machine C physical root](im-results/agent4-machine-c-global-path/README.md) · [#623 physical root](im-results/agent8-623-frontier/README.md) · [lasso-cylinder census](im-results/agent3-finite-lasso/README.md) · [coverage contract](im-results/agent8-coverage-contract/README.md).

## Mandatory research presentation

**NON-NEGOTIABLE PRESENTATION RULE:** Every research-facing README, board, index and note MUST give a coherent, self-contained account of the strongest established findings and remaining unknowns. **NEVER** make append-only progress logs, one-off execution or migration details, stale “pending” statuses, obsolete inventories, or superseded assertions the reader-facing account. **Whenever evidence changes, REWRITE and CONSOLIDATE the existing document in that same commit**, reconciling all contradictory claims and proof-status labels. Preserve useful derivations, counterexamples and provenance in a clearly labeled historical section or linked archive. **A chronological dump is a documentation defect and must be fixed before committing.**

Each active dossier should state its mathematical claim, exact original-source/proof status, evidence, unresolved quantifier, and next useful test near the top. Distinguish copied-model Lean checks, original-source certification, finite computation, paper argument, and conjecture. Preserve reproducibility and falsifiers when consolidating; link their durable archive.

## Working rules

Read the primary note and closest prior proof mechanism before starting substantial overlapping work. Prefer one maintained research dossier per coherent question. Check originality and dependencies before promoting a result. See the [research guide](RESEARCH_PROTOCOL.md) for scientific review and continuity.

**Maintainer rule: NEVER create a workflow that runs on every commit.** Invoke justified formal checks selectively with pinned source revisions.

Scheduler initialization, private identity ownership, memory boundaries, clock and release procedures remain governed by their original instructions. The [retired administrative design](research/archive/v1/README.md) and one-time migration records are historical material and impose no current grant, slot, checker, or renewal requirement.
