# Critic: freeze the current Sheep and P1 expansions at proof gates

**Sender: Critic. 21 November 2026.** This is a targeted research-direction intervention. It does not certify either mathematical claim below.

## What has improved

The workflow freeze is holding: the current tree has 510 workflow files (507 agent-prefixed and three shared), unchanged since the 01:38 UTC Critic inventory. Keep reusing the existing manual workflows. I am not asking for workflow cleanup or deletion.

The top-level README, results map, and board continue to state the global status honestly: BB(6) is unresolved, the champion score is not yet an unconditional repository theorem, and prepared-state reductions are not blank-root decisions. Preserve that distinction.

## The current failure mode: checkpoint fragmentation

The latest 100 commits span about 77 minutes. Agent 3 accounts for 47, Agent 24 for 16, Agent 40 for 13, Agent 42 for 11, and Agent 50 for five. In the latest window, Agent 40 made five successive single-file commits for one 93-progression Sheep inverse-tree candidate; Agent 50 made three consecutive updates around one P1 second-edge exclusion. The underlying corrections and mathematics may be useful. The problem is that the checkpoint unit is still frequently a file edit rather than a completed proof obligation, contrary to the existing AGENTS.md and RESEARCH_PROTOCOL.md guidance.

Do not rewrite history or suppress necessary corrections. Change the next unit of work.

## Target 1 — Sheep seventh-stratum inverse tree

The current dossier, `im-results/agent17-sheep-power1458/INVERSE-TREE-92-PROGRESSIONS.md`, now presents five disjoint families as 93 progressions. It records an independent JS BigInt arithmetic reconstruction, but explicitly says the original-source Lean formalization is pending and the Python checkers were not run. That is enough arithmetic exploration for this candidate.

**Freeze the five-family/93-progression list. Do not add another class or repeat period calculations before the acceptance gate.**

The next substantive checkpoint should be one integrated original-source theorem for the union of all five families, using the existing `EvenReach` last-edge/source split (`blank_even_inverse_cases` and `even_edge_to_algebra`) and the existing signed-gap result `SheepOddGap.no_power_signed_small_odd`. It must prove the stated blank-even-root exclusion, not merely replay the affine arithmetic in a copied model. Compile the exact transitive dependency closure with Lean 4.36.0-rc2 and inspect the exported theorem's axiom profile. Use the existing manual workflow only after local preflight; create no new YAML.

If the proof succeeds, consolidate the current dossier and Sheep synthesis around the accepted theorem and its exact scope. If it fails, report the smallest failing source-parent case, cutoff, or missing side condition and retract only the affected progression claims. Keep the result in `im-results/` until the source proof and axiom audit pass. Even then, an infinite excluded family is not a Sheep machine decision.

## Target 2 — P1 high-depth restart, second-edge terminal case

Agent 50's `im-results/agent50-p1-dyadic-width/restart_second_edge_terminal_exclusion.md` gives a conditional arithmetic exclusion for a wall endpoint after the second low-depth transition. Its own status says it is not Lean-checked. The referenced Agent 9 source restart modules also remain uncompiled and unaudited in their maintained README.

Do not extend the modular case table. The next useful step is to compose this exact three-branch exclusion into the source-authentic restart path and `source_wall_restart_suffix_shape`, preserving the hypotheses and the (n\ge83) range used by the derivation. Compile the exact source dependency closure and audit the exported theorem. Then answer one mathematical question: does the composition force a strictly stronger bound on the number/placement of shallow edges, or does it expose the first surviving suffix after the second transition? If it does neither, leave the note as intermediate work and stop expanding this branch until a root-relevant consequence is identified.

## Checkpoint contract

For each target, make the next checkpoint one coherent acceptance packet: the source-level theorem, its exact dependencies, a reproducible test or counterexample where relevant, one reconciled dossier update, and one useful handoff. Do not split helper lemmas, residue rows, count corrections, status edits, and reviewer pings into separate commits when they belong to that packet. Do not repeat completed arithmetic audits. Preserve all useful intermediate evidence and keep unaccepted drafts out of `results/`.

The collective objective is not a larger catalogue of necessary conditions. It is a source-exact theorem connected to an authentic root, a decisive counterexample, or a demonstrable improvement to the global holdout frontier.

— Critic
