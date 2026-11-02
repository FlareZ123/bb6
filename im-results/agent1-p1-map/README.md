# Agent 1: P1 counter-drain exploration (2026-11-02)

**Status: intermediate investigation only.** No new BB(6) halting/nonhalting decision or bound is claimed. This material belongs under `im-results/`, not `results/`.

Target 6-state, 2-symbol machine:
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

Primary source (formal acceleration and its Turing-machine correctness proof):
https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean

## Independent cross-check

The raw single-step simulator parses the 12 machine instructions directly from the six-state RLE string and begins at state A, position 0, on an all-zero tape. For every hub configuration `P1(a,c) = 0∞ 1^a A> 1^c 0∞`, it independently runs until the next P1 hub and compares its coordinates with the published accelerated map. It found exact agreement on **100 successive hub-to-hub transitions, encompassing 112,669 raw Turing-machine steps**. The first transition, from P1(0,0) to P1(2,1), took 6 raw steps. An attempt to extend the naive raw simulation to 1,000 hubs exceeded a 120-second local command timeout, so no claim is made for that run.

A separate simulation of the published accelerated map from P1(2,1) ran for 1,000,000 accelerated transitions without entering its halting gate. That is **computational evidence with no universal nonhalting implication**. It reached coordinates (1,376,716, 621,355), both measured exactly in Python integer arithmetic. At accelerated transition 45 the second coordinate first becomes positive and even; the naive proposed invariant "c always odd or zero" is therefore false.

## Kernel-checked conditional structure

A self-contained Lean 4 file `GParity.lean` defines the published nested recursion G and accelerated map T. Its four theorems were checked using Lean 4.36.0-rc2:

- `G_first_even`: all G outputs have even first coordinate.
- `G_preserves_odd_second`: G maps odd second coordinates to odd second coordinates.
- `T_none_iff`: T immediately halts exactly when the input second coordinate is 2 and the first is odd.
- `T_danger_predecessor`: an odd-first-coordinate, second-coordinate-2 output from T can only originate at a predecessor with even first coordinate and second coordinate 4.

The Lean axiom printout showed only standard Lean axioms `propext`, `Quot.sound`, and for the last theorem `Classical.choice`. No `sorryAx` was present after the successful final check. The Lean arithmetic proof checks the independently restated map, while the cited DeepMind formalization establishes correspondence with the original Turing machine. In isolation this local proof does not prove its own bridge to TM semantics.

## Next problem

Analyze reachability of the set `{P1(a,4) | a even}` from initial P1(2,1). The existing kernel-certified acceleration reduces the original halting question to dynamics on natural-number pairs. The gate lemmas are elementary and may already be implicit in the published work; no novelty is asserted. Attempt invariants, return-map renormalization and exact symbolic cover proofs. Use independent validation to avoid being misled by long numerical trajectories.
