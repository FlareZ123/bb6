# Exact-seed refinement of the #623 post-reset carry product

**Status:** exact finite-state structural observation; not an all-time root invariant or a machine-halting result.

## Main observation

The 395-state `post_reset_pair` DFA has 54 output labels. Each label is a complete `(L_final_state, R_final_state)` pair, not a set of possible pairs. `PostResetCarryOutputMap.md` records the 54/54 join of these labels with the 54 seed states in `PostResetCarryPairClosure.json`, including identical previous pairs and the invariant zero L y-carry.

Therefore, after a particular common reset has been recognized, the actual paired carry is one exact state ID in the 66-state closure. For any remaining suffix word `w`, deterministic transition gives one exact state `δ*(seed,w)`. This is the ordinary singleton-preservation identity:

`δ*({seed}, w) = {δ*(seed,w)}`.

## Consequence for the 211-state subset automaton

`NonSynchronizingSCCs.json` starts its subset construction from the entire 66-state set. Its 211 states represent images of that universal set under words. The 84 non-rank-one suffixes say that the suffix does not merge **all 66 possible seeds** to one state.

They do not represent uncertainty in the authentic carry after a common reset has supplied its exact output label. In particular, every recurrent component B1–B10 consists of nonsingleton image subsets (B1 and B2 each have 30 states of cardinality 2). A singleton seed path cannot enter any of these components: every deterministic transition preserves singleton cardinality.

This is a refinement, not a blanket synchrony assumption. Retain the 211-state automaton and all 84 exceptional suffix classifications as universal diagnostics and adversarial tests. For the authentic post-reset carry, however, track the exact seed ID and its deterministic path in the 66-state closure rather than treating a rank-greater-than-one universal image as actual carry ambiguity.

## Product design consequence

A source-faithful root product should distinguish:

1. the reset recognizer's exact output label / 66-state seed ID;
2. the deterministic 66-state carry reached after the post-reset suffix;
3. the next transition's independently computed target-own-start carry and boundary phase;
4. the universal 211-state subset/rank diagnostic, retained as a sidecar if the proof needs to certify all-start synchronization.

Do not identify the current output transducer's final carry with the next transition's own-start carry. The latter is recomputed from the next source state's low residues and drain corrections. This is the source-to-target versus target-own-start distinction already emphasized in `SourceCarryResetProduct.md` and `PostResetCarryOutputMap.md`.

## Scope and caveats

- The finite S-indexed scan accepts all 9,968 target windows D34–D10001, but this does not prove reset acceptance for every future root state.
- The exact-seed construction in `agent1-623-swindow-obstruction-product` used the retracted conservative S-window and its old counts must not be reused.
- The exact 54-label/54-seed join is a finite data check recorded by Agent48; a formal theorem should connect the DFA output labels to the 66-state `Allowed` invariant.
- The next-window product still has to compose the next source-to-target transducer, exact S-indexed shift/high extension, sector/branch phase, and weighted drain state. This note does not close that induction.

## Relevant artifacts

- `im-results/agent49-parity623/ResetPostStateDFA.json` — 54 full reset output labels.
- `im-results/agent49-parity623/PostResetCarryPairClosure.json` and `PostResetCarryPairInvariant.lean` — 54 seed IDs and the 66-state deterministic closure.
- `im-results/agent27-623-root-scan/NonSynchronizingSCCs.json` — 211 universal image subsets and recurrent nonsingleton components.
- `im-results/agent48-623-tight-window/PostResetCarryOutputMap.md` — exact 54/54 label-to-seed join and paired-output interface.
- `im-results/agent27-623-root-scan/SWindowPostResetSynchronization.md` — corrected S-window finite scan and the 84 universal nonsynchronizing suffixes.
- `im-results/agent24-machine623-shifted-reset-product/SourceCarryResetProduct.md` — exact one-window source-carry × reset-DFA composition and remaining root-transition obligations.