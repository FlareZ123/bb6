# Agent 50 — Raw10 Cryptids batch audit (preliminary, not proof)

I enumerated the 159 files in the pinned upstream `BusyBeaver/BB6/NonHalt` directory at commit `3647718b5df22e1a61462dec0376bd204526285a`, applied all six state permutations fixing the raw10 parent transitions A0=1RB and B0=1LC, and tested each one-halt leaf against the exact 41-box residual complement from `Raw10Encoded.lean` plus the cycle/halt certificates.

Results of this finite crosswalk:
- 73 source modules have at least one A/B-fixing raw10 alias.
- 62 modules have all six aliases outside the historical 663 holdout list and outside the six already integrated roots, with each 25-completion leaf wholly contained in one residual box.
- Those 62×6 aliases are pairwise disjoint: 372 candidate leaves, total union mass 9,300.
- Adding all 372 as separate remainder certificates expands the exact complement from 41 boxes to 1,967 boxes while reducing mass only from 90,737,503,713,725 to 90,737,503,704,425.

This is only a computational candidate crosswalk: it does **not** establish that the 62 upstream theorem modules compile under our dependency overlay, nor that the 372 state-renamed adapters have been proved. The single current pilot is one of these leaves and remains pending CI.

**Recommendation:** do not bulk-add these 372 atoms to the explicit remainder list. The mass reduction is negligible and the rectangle count explodes. Complete the single source-backed pilot, then either prove its six state-renamed aliases through a reusable renaming lemma or prioritize a genuinely larger cylinder / parent-level closure. Keep the current complement representation stable unless a compact union/decision-diagram consumer is developed.

Reproduction inputs: `im-results/agent49-box-complement/Raw10Encoded.lean`, `im-results/agent50-weighted-tnf-pilot/Raw10Box8Cycle.lean`, `im-results/agent50-weighted-tnf-pilot/Raw10Box0Halt.lean`, `resources/BB6_holdouts_663_2026-10-16.txt`, and the pinned upstream directory above. This audit belongs in `im-results/`, not `results/`.
