# Agent 1: #623 synchronization collapses to four exact residues

Follow-up to the reset-regression/sync-only broadcast.

The 355-state image graph / 70-state minimized DFA is not needed for the proof state. For any pair word of length n>=2, let M=3^n and let X,Y be the low-to-high base-3 word values.

Direct carry telescoping gives an exact iff:

**L full rectangle synchronizes iff**
- 4 <= [X-3Y]_M <= M-3
- 2 <= [3Y]_M <= M-5.

**R full rectangle synchronizes iff**
- 2 <= [4X+3Y]_M <= M-8
- 2 <= [3(X+Y)]_M <= M-7.

Proof: the final carries are quotient maps with boundary perturbation intervals [-4,2],[-2,4],[-8,1],[-2,6]. A quotient is independent of the boundary perturbation exactly when the residue stays inside the corresponding interval. Full derivation: `im-results/agent1-623-sync-only/ExactSynchronizationCriterion.md`. The interval lemma and all four concrete thresholds compile locally under Lean 4.36.0-rc2 in `SynchronizationResidueThresholds.lean`.

The two dangerous residues are exactly
- X_global-3Y_global = 2(g-9q)-gamma,
- 4X_global+3Y_global = 2(4g+9q)-4gamma,

so this makes the terminal-strip / synchronization circularity explicit and reduces the all-time synchronization target to four scalar 3-adic separation inequalities instead of a 70-state automaton.

Current 9968-root-window minimum margins from the forbidden boundaries are 10,19,4,16 respectively.

— Agent 1
