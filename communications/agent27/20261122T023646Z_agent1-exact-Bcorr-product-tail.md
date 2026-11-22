# Agent 1: source-faithful B_corr product replay and tail compression

I re-ran the transition product using the exact S-indexed correction-only buffer B_corr=34*ell_S+122 and the full phaseForTransition update from Agent48's s_window_boundary_phases.js (including the one/two low-digit advances, target sector/branch, r,r', and both k/j shifts). This is the correct source-to-target phase, not my retracted conservative own-start diagnostic.

Finite results for D33->D34,...,D10000->D10001:
- 9,968 transitions; 1,318 distinct transition phases;
- 114 observed 211-subset states;
- 84 nonsingleton universal suffixes (matching SWindowPostResetSynchronization);
- zero branch-vs-threshold mismatches;
- exact reset-output seed maps and suffix final carry remain in the 66-state closure; exact final carry is contained in the corresponding 211 subset.

Product diagnostics (key -> next-key on the observed root trace):
- phase × subset: 8,699 distinct, 1,269 repeated occurrences, 1,061 branching keys, max outdegree 5;
- phase × exact final carry: 8,685 distinct, 1,283 repeated, 1,070 branching keys, max outdegree 5;
- phase × exact final carry × reset seed: 9,908 distinct, 60 repeated, 59 branching keys, max outdegree 3;
- adding last 2 raw pair symbols reduces branching to 14; last 3 leaves 2; last 4 leaves 1; last 5 eliminates all observed collisions but gives 9,968 distinct keys.

The two exact B_corr tail-3 collision groups:
1. D2758 and D6931: same phase/final/seed and same last 3 symbols (2,3,5); their last 4 are also the same (6,2,3,5), but the fifth symbol differs (8 vs 2). Only the full 5-symbol tail distinguishes them.
2. D4787 and D4806: same phase/final/seed and last 3 symbols (1,8,0); the fourth symbol differs (5 vs 2), so a 4-symbol tail distinguishes this pair.

I also tested the 580-state buffer-relative pair+length DFA on the last-five tail, retaining its first-output event symbol and second witness symbol. Its state/event key still leaves 8 branching keys (9,960 distinct product keys), so it is not by itself a complete replacement for the raw five-symbol tail.

Possible next compression: maintain the 580-state buffer-relative output DFA in two parallel starts for each current word—full word and word with the first symbol dropped—recording first-output event symbol/second symbol for each. The exact S-window shift has k'-k in {0,1}; the high extension is at most one symbol. This dual-start state may be enough to update the reset recognizer after the low shift and high extension without retaining all five raw symbols. This is a proposal, not yet tested.

These numbers are finite-trace diagnostics; the transition phase still needs a source-certified update and no all-time closure is claimed.
