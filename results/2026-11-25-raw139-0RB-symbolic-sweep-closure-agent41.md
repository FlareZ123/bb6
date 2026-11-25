# Raw139 F/1 = 0RB: source-certified exhaustive weighted closure

**Theorem.** Every compatible completion of the literal partial table `[7,24,11,24,14,21,3,16,12,11,24,5]` satisfies `WeightedBound 290` in the project's weighted six-state semantics. This is an exhaustive certificate for the entire three-hole cylinder, not a finite-run claim. The theorem is `BB6.Agent41F1ZeroRB.all_completions_weighted`.

**Proof status.** Original-source Lean 4.36.0-rc2, standard axioms only, [successful pinned run 45609382340](https://github.com/FlareZ123/bb6/actions/runs/45609382340), source revision `464020270a1d82800bcebb7071831e58ac911bc7`, compiled artifact `15018818460`. The reproduction script checks the final theorem, checked wrapper, symbolic interpreter soundness theorem, both non-affine growth mechanisms, and all 23 nonhalting leaf theorems. The transitive axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or `native_decide` occurs in the audited profiles.

The complete tree has 20 internal splits and 461 terminal leaves: 194 translated cycles, 164 last-hole queries, 80 FAR certificates, and 23 all-time growth proofs. The maximum last-hole query is 241; the uniform weighted bound is 290.

## Reusable mathematical contribution

The proof reuses the symbolic zipper interpreter `Agent41SymSweep.lean`, which treats each unexamined finite tape segment as an opaque gap and rejects any symbolic execution that reads into a gap. The original-source theorem `run_sound` transports a successful symbolic trace to every assignment of the gaps. This permits exact sweep recurrences over arbitrary suffixes, rather than extrapolation from sampled runs.

Two of the 23 exceptional leaves require non-affine recurrences:

- **H19, unary drain.** After 55 blank-start steps, stage `param 0` has state A, left word `01`, and right word `011111 · (111)^n · 001111`. Entry costs (15n+32) and initializes (a=6+3n,b=0). In state C, the inner word `01 · 1^a · 00 · 1^(6+b)` drains (a) by one, adds three to (b), and costs (4a+12). Structural induction reaches (a=0,b=3(6+3n)); the exit costs (3b+50) and produces stage `param (3n+7)`. All stage costs are positive, proving nonhalting for every completion.
- **H20, binary increment.** After 55 steps, the right tape contains `011111 · (111111111)^n · 001111`. Entry costs (9n+51). The inner fixed-length little-endian word begins `[false,true,false]` followed by (3n) zero bits (true encoded by 111, false by 100). Each increment with (k) trailing low-order ones costs (12k+30), preserves length, and never reads beyond the arbitrary suffix. The rank `zeroRank`, interpreting the complemented bits as a little-endian natural, decreases by exactly one. Well-founded induction proves termination of the inner increment loop without a fuel cutoff; the outer exit then reaches stage (n+1). This is a genuine all-time nonhalting proof, despite exponentially long inner loops.

The remaining 21 growth leaves use affine or phase/block recurrences. Exact source details and reproduction commands are in the [full 0RB dossier](../im-results/agent41-raw139-f1-zeroLF/ZeroRB.md) and [sibling certificate map](../im-results/agent41-raw139-f1-zeroLF/README.md).

## Consequence and limitation

This closes one exact raw139 depth-five F/1 sibling at weighted bound 290. It is pairwise disjoint from the separately certified 0LF and 0RC siblings because the assigned F1 transition differs. Its exact graft into the global champion-score residual frontier is a separate proof obligation: the current 106-leaf raw139 consumer still includes 0RB, and the proposed 106-to-105 filter is only a draft pending a full original-source consumer/axiom audit. No global residual count is reduced by this result alone. The universal BB(6) upper bound remains open.
