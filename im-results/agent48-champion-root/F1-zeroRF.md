# Raw139 F/1 = 0RF: source-accepted complete cylinder certificate

**Status (25 November 2026): original-source Lean 4.36.0-rc2 acceptance passed.** The exact depth-five champion-path sibling table is `[7,24,11,24,14,21,3,16,12,11,24,21]`, ordered A0,A1,...,F1; code 24 denotes an unassigned transition. A/1, B/1, F/0 remain unassigned. This is a strict descendant of raw139, not a complete canonical representative.

The complete certificate proves `WeightedBound 211` for every compatible completion, including the weighted blank-delay and final-query convention. Its original-source audit passed in [GitHub Actions run 45581070284](https://github.com/FlareZ123/bb6/actions/runs/45581070284), job `champion_parent`, on a source revision containing certificate commit `ff8e6727de052f0322bd6b6ccc10e3cd994f266e`. The job ran `im-results/agent48-champion-root/reproduce-parent.sh`, which compiled the exact import closure and checked the exported theorem axiom profiles against the standard allowlist; the forbidden-placeholder guard also passed.

## Mathematical closure

The first-hole audit tree has 7 split nodes, 117 translated side-cycle leaves, 30 last-hole leaves, 14 FAR leaves (DFA sizes one or two), and one explicit growing-tape leaf. The largest reached first-hole index is 205, giving the weighted bound 211. The generator is `generate-f1-zeroRF.cjs`; `node generate-f1-zeroRF.cjs > ChampionF1ZeroRFCover.lean` regenerates the full tree. The Lean checker is the existing `FastThreeHoleAudit.fastCheck`, not the generator.

The sole non-FAR growth leaf has table `[7,13,11,24,14,21,3,16,12,11,14,21]`, with B/1 unassigned. Write zipper words nearest-head first, with the left word including the scanned cell. Define

- F = 10111, P = 000011, W = 010111, D = 111, S = 01;
- Q0 = 00111111, Q1 = 0000001111, Q2 = 101111, Q3 = 11110111.

After 192 transitions from blank, the machine is in state F with left word F and right word P Q0 S. At stage n the right word is P^n Q0 S^n. The right sweep transfers each P to a W on the left in 8 transitions; the left sweep restores each W to a P in 10. Four exact central turns (12, 18, 22, 58 transitions) change Q0 to Q1, Q1 to P Q2, Q2 to Q3, and Q3 to Q0 S. The latter two phases use n+1 blocks. Each left sweep ends with a 12-transition return. Thus

```
run0 ctr (72*n + 194) (atStage n) = some (atStage (n+1))
```

for every n, with positive cost. The imported `SweepPumping.never_of_growth` transports this unbounded family to the original machine semantics for every compatible completion. B/1 is never queried. The parametric block sweeps and four turns are definitional equalities checked by Lean; this is an all-time nonhalting proof for the exceptional leaf, not a finite simulation.

## Source-consuming contract and remaining integration

- `ChampionF1ZeroRFHard.lean` proves the exact entry, four central turns, block sweeps, stage recurrence, and universal `NeverHalts` theorem.
- `ChampionF1ZeroRFCover.lean` assembles the complete `WeightedBound 211` audit tree and proves `all_completions_weighted`.
- `ChampionF1RFIntegration.lean` proves that this parent is exactly `championChild 5 ⟨false,true,5⟩), removes exactly one entry from the prior 110-leaf F1 complement, and states a conditional exactness theorem with 109 raw139 leaves plus the 77 other canonical-78 representatives.

The standalone cylinder certificate is source-accepted. The consuming 109-leaf theorem is **not yet source-accepted**. Full integration run [45577606094](https://github.com/FlareZ123/bb6/actions/runs/45577606094) failed in upstream exact-score wrappers before reaching the frontier modules. Those wrappers have since been patched on main using symbolic score bounds; downstream frontier defects were also corrected (symbolic champion-step room, direct residual-list membership, correctly aligned mixed-roster bounds, and the parent identity proof). Two subsequent dispatches, [45601313596](https://github.com/FlareZ123/bb6/actions/runs/45601313596) and [45602044422](https://github.com/FlareZ123/bb6/actions/runs/45602044422), were cancelled before completing the full source closure after further source review. Neither is a verification result and neither weakens the standalone cylinder certificate.

The proposed 109 count remains a kernel-decidable calculation inside the draft consumer, not an accepted global frontier reduction. Current main contains 38 certified champion witnesses at depths 1/2/3/4/5/6 = 1/3/8/7/9/10, giving the correct 146/254 base counts; replacing the final A1 split gives 123, and the downstream chain remains 113 → 112 → 110 → 109. Agent41's separate F1=0LF whole-cylinder certificate is now source-accepted in run [45604778890](https://github.com/FlareZ123/bb6/actions/runs/45604778890). Its exact parent-to-list integration remains pending and should reduce 109 to 108 once proved. The 109 integrated theorem itself has not yet passed a complete source audit. Even after integration, 77 other canonical-78 representatives remain separate obligations. No global upper bound, exact BB(6) value, or equality claim follows from this cylinder alone.
