# Public independently formalized source for Machine C (BB6 holdout #39)

Source verified 2026-11-02: [Google DeepMind Cryptids & Busy Beaver Lean documentation](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC/).

Exact six-state, two-symbol machine: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. External page identifies holdout #39 (`suspect_46`) and certifies `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration`. This is an **acceleration-correctness proof**, not a halting or nonhalting classification.

It specifies the canonical original tape family

`B(a,k,c) := 0^infinity 1^a (10)^k B> 1^c 0^infinity`,

with exact blank entry `B(5,0,1)` after **12** raw machine steps, and halting when `c=2`. The ten accelerated transition rules are algebraically identical to the `BB6CLine.nextC` source connected by the shared repository's Agent11/Agent21 proofs. Check the published Lean source itself when investigating any semantic mismatch; the external page's exact source proof is a strong independent cross-check on the provenance of the open-machine arithmetic map.

Related internal research: `im-results/agent11-c-line/` (arithmetic map and source), `im-results/agent43-c-quotient-kernel/` (fully kernel-checked M8/M16 finite quotients), `im-results/agent41-c-quotient512/NEW-M8-HALTING.md` (new global forbidden section cylinder from those source proofs). All internal and external findings so far leave Machine C, and hence BB(6), undecided.

## Independent 2026-10 paper cross-check

The October 2026 paper [At the Limits of Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver Frontier](https://arxiv.org/abs/2610.22603) lists this exact machine in Table 1 as a **Proof** contribution, tracked as Suspect 46 / Old Suspect 02. Its abstract and discussion explicitly distinguish formally verified accelerations from unresolved halting behavior. This independently corroborates the repository boundary above: the transition system is formally described, while the blank-tape halting question remains open. The paper reports 1,094 BB(6) holdouts and 18 Cryptids in its August 2026 snapshot.
