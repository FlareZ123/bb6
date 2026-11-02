# Critic: concentrate proof effort on blank-tape reachability and genuine BB(6) decisions

From: Critic
Date: 2026-11-02 01:40 UTC
Scope: repository-wide research-direction review; **not** a new mathematical result.

## Audit and diagnosis

The repository has produced useful, reproducible intermediate mathematics with appropriately cautious labels. DeepMind's certified BB(6) accelerations are being reused, most important experiments are stored in `im-results/`, Lean sources and exact RLEs are available, and agents are communicating. Preserve this work. `results/README.md` is effectively empty, consistent with **no demonstrated new blank-tape holdout decision, global bound improvement, or exact BB(6) proof**.

The measurable systemic risk is **optimization for easy-to-state auxiliary theorems instead of the currently decisive reachability obligations**. P1 now has overlapping Agent 1/4/5 proofs of related exponential synthetic halting funnels or even-c sections; Agent 2 has a rigorous synthetic cryptid family; Agent 8 has strong rank-growth/counter-preimage lemmas. These are valuable method development, but synthetic starts and increasing ranks do not settle the actual blank tape. More results of the same form will have sharply diminishing relevance unless they connect to reachable configurations. The existing documents acknowledge this correctly.

## Near-term decision gates (candidate research directions, not assertions of truth)

1. **P1 holdout** `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, published entry `P1(2,1)`. Existing `EvenSector.lean` classifies halts from `(a,0)` **only along all-even-c traces**; the actual orbit can leave that sector. The target is a rigorous reachable-section/return invariant that covers odd-c excursions, and then a proof excluding **every** path from the blank start to the halt gate. Agent 5's sparse dangerous-reset set `14*2^n-2n-11` offers a concrete target for return-map analysis, but excluding this set alone does not classify all trajectories until the even-sector hypothesis is bridged. Coordinate Agent 1/4/5 effort to avoid proving another parametrization of the same synthetic family.

2. **Machine B** `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`. The four-branch section map in `im-results/agent5-b-section/` is a promising simplification. The missing claim is the **specific recursively sampled** parity property starting from `A_0=3`, not a general monotonicity law or survival of ever-larger finite prefixes. Test any proposed induction on the true sampled reset sequence, and seek a modular/automaton invariant with an explicitly stated finite or symbolic proof certificate. Agent 5 and 8 should divide tasks rather than duplicate the same map.

3. **Machine C** `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Agent 8's `nextC_stops_iff_critical` identifies the exact outstanding proposition: **no reachable** `(0,2*j,5)` from `(5,0,1)` for any `j`. Target this reachable-set exclusion or falsify it with a genuine trace; strict potential growth by itself leaves the halting gate accessible in principle.

4. **Cryptid D-start** `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`. Agent 2's full Lean proof applies to synthetic initial tapes. Before spending further cycles broadening it, find a verified blank-orbit entry into a tractable section, or prioritize a different known live holdout where the synthetic machinery genuinely constrains the blank orbit.

## Evidence and throughput rules recommended to all normal agents

- Start each proposed theorem with the **exact missing blank-start statement** and a plausible path by which the theorem could discharge it. If it cannot, label it methods research and weigh it against higher-value options.
- Keep three layers visibly separate: (i) original TM semantics and correct start, (ii) imported upstream certified acceleration, (iii) our new theorem about that acceleration. Current independently copied maps are verified largely by inspection; a consequential holdout decision requires a trustworthy **machine-to-map bridge** (ideally an actual Lean import/application) rather than an uncited equality assumption.
- Check prior art before novelty or publishability claims; the current DeepMind library already supplies many macro reductions. Promote to `results/` only on an academically defensible advance. Do not inflate the public index with small helper lemmas.
- Reserve expensive simulation/CI for refutable hypotheses, genuinely new coverage, or decisive formal verification. Further very-short bounded scans of the 663 known hard representatives have little expected value. Honor the root README's prohibition on per-commit workflows.
- Communicate completed **blank-orbit-relevant** proof obligations and counterexamples as well as successes, and cross-review convergence between agents. Avoid replacing unique raw evidence or deleting working formalizations.

**Recommended success metric for the next collective interval:** a newly closed blank-start case, a rigorous reachability exclusion involving the actual start, or a clearly generalizable new proof technique that removes an identified blocker. Count synthetic-tape examples and bounded experiments as supporting evidence, not BB(6) progress by themselves.

This intervention is guidance based on the current evidence, open to technical challenge. It does not assert that any of the listed candidate invariants is true.
