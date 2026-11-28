# BB(6) research

Collaborative research toward a rigorous determination of the six-state, two-symbol, blank-tape Busy Beaver **step** value. This repository contains original-machine formalizations, mathematical reductions, inverse and forward invariants, finite checks, and experimental leads.

**Research state (28 November 2026): BB(6) remains unresolved.** The strongest source-accepted conditional maximality interface is **Canonical38**. [Run 46150267242](https://github.com/FlareZ123/bb6/actions/runs/46150267242) consumes the accepted complete Raw112 parent Cover on the authenticated Raw39 [Canonical39 predecessor](results/2026-11-28-canonical39-raw39-global-source-accepted-agent3.md), leaving exactly **38 residual Cover hypotheses**. The source-accepted fixed-score theorem `BB6.Agent10Raw112Canonical38AfterRaw39.exact_at_champion_score` has only the standard Lean axiom profile; artifact **15265958695** records this reduction. The separately source-certified exact champion score and blank-start witness do not prove universal maximality. See the [Canonical38 result](results/2026-11-28-canonical38-raw112-after-raw39-source-accepted.md), [current board](research/BOARD.md), and [mathematical results map](results/README.md). No exhaustive six-state maximality certificate has been established.

Note from maintainer: if your GitHub tool doesn't let you run workflows, use the Github Actions MCP, it is a different tool but it works.

## Start here

| Document | Purpose |
| --- | --- |
| [Results map](results/README.md) | Established statements, verification scope, and missing global proof obligations |
| [Research board](research/BOARD.md) | Research questions, bottlenecks, and primary dossiers |
| [Research guide](RESEARCH_PROTOCOL.md) | Scientific practice and continuity |
| [Investigation notes](research/issues/README.md) | Research questions with historical context |
| [Reference resources](resources/START_HERE.md) | Source context and orientation |
| [Agent guidance](AGENTS.md) | Repository-specific agent instructions |

## Decision gates toward an exact BB(6) proof

**An exact answer requires both sides:** (1) a genuinely halting six-state machine with an **exact primitive-transition count**, and (2) a proof-carrying **universal upper bound** covering every other six-state, two-symbol blank-start machine. The first obligation is now complete for the published champion: [the exact source-certified step score](results/2026-11-24-champion-exact-attainment.md). The universal upper bound remains open.

These are **unclosed all-time proof obligations**, not a leaderboard of residue or inverse-family counts. Follow the linked maintained dossiers for formulas, source commits, compiler outcomes, conditional calculations and counterexamples.

| Programme | Strongest relevant leverage | Proof still needed |
| --- | --- | --- |
| **Global exhaustive classification** | [Weighted first-one normalization](im-results/agent13-weighted-first-one/README.md), complementary [source-queue and physical-trace routes](research/BOARD.md), and the source-accepted [Canonical38 Raw112-after-Raw39 reduction](results/2026-11-28-canonical38-raw112-after-raw39-source-accepted.md) (run **46150267242**, artifact **15265958695**). | Prove a score-B `Cover` for each of the **38** retained quotient representatives. The accepted complete Raw47 local parent is the next global-consumption candidate, but its exact membership/removal must be proved on the accepted Canonical38 lineage (or an independently accepted equivalent join); do not decrement the count arithmetically. Only discharging every remaining Cover establishes the universal upper bound. |
| **TM1 champion / TM63** | [Complete exact named-table halting and attainable score](results/2026-11-24-champion-exact-attainment.md), compiled locally with Lean 4.36.0-rc2 and standard axioms only. | **Closed for the candidate.** To prove maximality, supply an exhaustive certificate bounding every other machine by this exact score. |
| **Cryptid D family** | [Global total affine/quadratic source reduction and executable halting equivalence](results/2026-11-24-d-global-affine-completeness-agent32.md); [four original blank-start section bridges](im-results/agent3-portfolio-raw-conjugacy/README.md). | Compose the exact section semantics across the four authentic seeds I9, I5, I15 and I39; prove a terminal accelerated block or all-time terminal avoidance for each root. Prepared-state cylinders and finite replays do not decide these roots. |
| **Pinned Cryptid #85 candidate** | [Source-level stack and reset recurrences](im-results/agent12-cryptid-root-invariant/README.md), with conditional continuation and bounded replay. | Close the authentic token/3-adic itinerary and all remaining branches, with a source-faithful halt or nonhalt proof. Conditional raw totals are not certified lower bounds. |
| **Machine C** | [Joint exact stopping criterion](im-results/agent19-c-odd-dyadic/JointCriterionIntegration.md), verified original-source predecessor exclusions and [strict image results](results/2026-11-09-machine-c-all-depth-strict-section-image-hierarchy-agent4.md). [Recent M16 work](im-results/agent13-residual-frontier/) distinguishes compiled quotient theorems from source-only or uncompiled parent closure. | Eliminate **all** remaining low/high halting parameters along the genuine blank orbit, or exhibit an actual halt. An infinite family of exclusions is still not a Machine C decision. |
| **P1** | [Critical-gateway and reset-cost certificates](im-results/agent43-p1-high-cost-reset-count/README.md); [inverse shadow work](im-results/agent9-p1-shadow/README.md) includes rigorous local inverse phenomena. | Resolve every surviving inverse exit and its authentic blank-root correspondence. A long legal prepared inverse path need not reach the blank start. |
| **Space Needle** | [Original-source terminal-feeder modular obstructions](im-results/agent48-space-needle/README.md) and [two-step inverse constraints](im-results/agent46-needle-two-step/README.md). | Cover the remaining valuation/parent branches and prove an all-time blank-orbit decision. Modular-density exclusions are not machine nonhalting. |
| **#429 and #746** | [#429 original gate reductions](im-results/agent6-harmonic429/README.md); [#746 inverse grammar and surviving-index analysis](im-results/agent10-cascade/README.md), with [genuine infinite root-index exclusions](results/2026-11-19-machine-746-rho20-infinite-subfamily-root-exclusion.md). | Replace partial inverse-tree reductions with a **complete blank-root halt/nonhalt decision** for each machine; unbounded inverse fan-in blocks naive fixed-depth closure. |

**Research decision:** Prefer the next *source-accepted missing edge in a complete proof chain* to another disconnected finite scan, residue catalogue, uncompiled downstream wrapper, or duplicate CI workflow. For each claim, distinguish original-machine proof, conditional prepared-tape theorem, finite experiment, and paper-level derivation. The [research board](research/BOARD.md) maps individual active blockers; the [results map](results/README.md) lists stronger publishable claims and their evidence boundaries.

The former detailed root-level inventory is preserved as a [dated historical snapshot](research/archive/root-readme-detailed-2026-11-23T1900Z.md); **it is not current status**. Update the relevant maintained dossier and research board when mathematics changes, and keep this entry point concise.

## Mandatory research presentation

**NON-NEGOTIABLE PRESENTATION RULE:** Every research-facing README, board, index and note MUST give a coherent, self-contained account of the strongest established findings and remaining unknowns. **NEVER** make append-only progress logs, one-off execution or migration details, stale “pending” statuses, obsolete inventories, or superseded assertions the reader-facing account. **Whenever evidence changes, REWRITE and CONSOLIDATE the existing document in that same commit**, reconciling all contradictory claims and proof-status labels. Preserve useful derivations, counterexamples and provenance in a clearly labeled historical section or linked archive. **A chronological dump is a documentation defect and must be fixed before committing.**

Each active dossier should state its mathematical claim, exact original-source/proof status, evidence, unresolved quantifier, and next useful test near the top. Distinguish copied-model Lean checks, original-source certification, finite computation, paper argument, and conjecture. Preserve reproducibility and falsifiers when consolidating; link their durable archive.

## Working rules

Read the primary note and closest prior proof mechanism before starting substantial overlapping work. Prefer one maintained research dossier per coherent question. Check originality and dependencies before promoting a result. See the [research guide](RESEARCH_PROTOCOL.md) for scientific review and continuity.

**Maintainer rule: NEVER create a workflow that runs on every commit.** Invoke justified formal checks selectively with pinned source revisions.

Scheduler initialization, private identity ownership, memory boundaries, clock and release procedures remain governed by their original instructions. The [retired administrative design](research/archive/v1/README.md) and one-time migration records are historical material and impose no current grant, slot, checker, or renewal requirement.
